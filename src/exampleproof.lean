import WZtheorem

open int

/-
Proof of ∑ₖ (binomial n k) / (2^n) = 1.
-/

namespace binomial

def binomial : ℕ → ℤ → ℚ
  | 0 0 := 1
  | 0 _ := 0
  | (n+1) k := binomial n k + binomial n (k-1)

theorem binomial_neg_zero (n : ℕ) : ∀ k, (k < 0) → binomial n k = 0 :=
begin
  induction n with d hd,
  {
    intro k,
    intro hkneg,
    cases k,
    {
      cases k,
      {
        simp at hkneg,
        exact false.rec (binomial 0 (of_nat 0) = 0) hkneg,
      },
      refl,
    },
    {
      refl,
    }
  },
  {
    intro k,
    intro hkneg,
    rw binomial,
    rw hd k hkneg,
    rw hd (k-1) _,
    exact add_zero 0,
    linarith,
  }
end

theorem binomial_gt_n_zero {n : ℕ} : ∀ (k : ℤ), k > n → binomial n k = 0 :=
begin
  induction n with d hd,
  {
    intro k,
    intro hkpos,
    cases k,
    { 
      cases k,
      {
      simp at hkpos,
      exact false.rec (binomial 0 (of_nat 0) = 0) hkpos,
      },
      {
        rw binomial,
        linarith,
      }
    },
    {
      rw binomial,
      linarith,
    }
  },
  {
    intro k,
    intro hkgtds,
    rw binomial,
    have hds : d.succ = d+1 := rfl,
    rw hd k _,
    rw hd (k-1) _,
    exact add_zero 0,
    rw hds at hkgtds,
    linarith,
    rw hds at hkgtds,
    linarith,
  }
end

lemma binomial0sum : ∀ m, summation.summation (binomial 0) m = 1 :=
begin
  intro m,
  induction m with d hd,
  {
    rw summation.summation,
    refl,
  },
  {
    rw summation.summation,
    rw hd,
    rw binomial,
    rw binomial,
    ring,
    linarith,
    {
      refine ne.elim _,
      refine neg_ne_zero.mp _,
      simp,
      linarith,
    },
  },
end

end binomial

open binomial

def F : ℕ → ℤ → ℚ := λ n k, (binomial n k) / (2 ^ n)

def G : ℕ → ℤ → ℚ := λ n k, - (binomial n (k-1)) / (2 ^ (n+1))

theorem WZ_FG : WZ_pair F G :=
begin
  unfold WZ_pair,
  intros n k,
  rw F at *,
  rw G at *,
  simp,
  rw binomial at *,
  ring_nf,
  simp,
  ring_nf,
  refine sub_eq_zero.mp _,
  simp,
  ring_nf,
  rw zero_eq_mul.mpr,
  left,
  refine sub_eq_zero.mpr _,
  refine inv_inj'.mp _,
  simp [inv_inv],
  rw mul_inv',
  simp [inv_inv],
  rw pow_succ,
  ring,
  exact domain.to_no_zero_divisors,
end

theorem Gvanishes : ∀ n, vanishes (G n) :=
begin
  intro n,
  unfold vanishes,

  intro ε, intro hεpos,
  rw G at *,
  simp,
  use (n+1),
  intro k,
  intro hkrange,
  cases hkrange,
  {
    split,
    rw binomial_gt_n_zero,
    simp,
    assumption,
    {
      push_cast at hkrange,
      linarith,
    },
    {
      have hkpgtn : k-1 > n :=
      begin
        push_cast at hkrange,
        linarith,
      end,
      rw binomial_gt_n_zero (k-1) hkpgtn,
      simp,
      assumption,
    }
  },
  {
    have h : k - 1 < 0 :=
    begin
      induction n with d hd,
      {
        push_cast at hkrange,
        linarith,
      },
      {
        push_cast at hd,
        push_cast at hkrange,
        have h' : k < -(d + 1) := by linarith,
        exact hd h',
      }
    end,
    split,
    rw binomial_neg_zero,
    simp,
    assumption,
    exact h,
    rw binomial_neg_zero,
    ring_nf,
    assumption,
    exact h,
  }
end

theorem basecase : summation.equals_indefinite_sum (F 0) 1 :=
begin
  rw summation.equals_indefinite_sum,
  intro ε,
  intro hεpos,
  unfold F,
  simp,
  use 0,
  intro m,
  intro hmgt0,

  rw binomial0sum m,
  split,
  linarith,
  linarith,
end

-- the final theorem
theorem binomial_id : ∀ (n : ℕ), summation.equals_indefinite_sum (F n) 1 := WZ WZ_FG Gvanishes basecase