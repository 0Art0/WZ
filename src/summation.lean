import data.rat.basic
import data.rat.floor

namespace summation -- this file contains all the necessary definitions and theorems about summations required for the proof of the WZ theorem

-- an inductive definition of summation over a subset of ℤ
def summation (f : ℤ → ℚ) : ℕ → ℚ
  | 0 := f 0
  | (m+1) := f (-(m+1)) + summation m + f (m+1)

-- finite summations split
theorem summation_split {f g : ℤ → ℚ} {m : ℕ} : summation (λ (n : ℤ), f n + g n) m = summation f m + summation g m :=
begin
  induction m with d hd,
  refl,
  rw [summation, hd, summation, summation],
  ring,
end

-- finite differences split
theorem difference_split {f g : ℤ → ℚ} {m : ℕ} : summation (λ (n : ℤ), f n - g n) m = summation f m - summation g m :=
begin
  induction m with d hd,
  refl,
  rw [summation, hd, summation, summation],
  ring,
end

-- scaling the summands scales the sum by the same amount
theorem summation_scaling {f : ℤ → ℚ} {c : ℚ} {m : ℕ} : summation (λ n, c * f n) m = c * (summation f m) :=
begin
  induction m with d hd,
  refl,
  rw [summation, hd, summation],
  ring,
end

-- this is true when ∑_{n ∈ ℤ} f n = c
-- the summation is defined as a limit of finite sums
def equals_indefinite_sum (f : ℤ → ℚ) (c : ℚ) := ∀ (ε : ℚ), ε > (0 : ℚ) → ∃ (M : ℕ), ∀ (m : ℕ), m > M → (summation f m > c - ε) ∧ (summation f m < c + ε)

-- indefinite summations split
theorem indefinite_summation_split {f g : ℤ → ℚ} {c d : ℚ} (sf : equals_indefinite_sum f c) (sg : equals_indefinite_sum g d) : equals_indefinite_sum (λ (k : ℤ), f k + g k) (c + d) :=
begin
  rw equals_indefinite_sum at *,
  intro ε, intro hε_pos,

  have hεbytwo_pos : (ε / 2) > 0 := half_pos hε_pos,

  cases sf (ε / 2) hεbytwo_pos with Mf hsf,
  cases sg (ε / 2) hεbytwo_pos with Mg hsg,

  use Mf + Mg,

  intro m,
  intro hmlarge,

  rw summation_split at *,

  have hm_gt_Mf : m > Mf := by linarith,
  have hm_gt_Mg: m > Mg := by linarith,

  cases hsf m hm_gt_Mf with fbound_low fbound_high,
  cases hsg m hm_gt_Mg with gbound_low gbound_high,

  split,
  {
    linarith,
  },
  {
    linarith,
  }
end

-- indefinite differences split
theorem indefinite_difference_split {f g : ℤ → ℚ} {c d : ℚ} (sf : equals_indefinite_sum f c) (sg : equals_indefinite_sum g d) : equals_indefinite_sum (λ (k : ℤ), f k - g k) (c - d) :=
begin
  unfold equals_indefinite_sum,
  intro ε, intro hε_pos,

  have hεbytwo_pos : (ε / 2) > 0 := half_pos hε_pos,

  cases sf (ε / 2) hεbytwo_pos with Mf hsf,
  cases sg (ε / 2) hεbytwo_pos with Mg hsg,

  use Mf + Mg,

  intro m,
  intro hmlarge,

  rw difference_split at *,

  have hm_gt_Mf : m > Mf := by linarith,
  have hm_gt_Mg: m > Mg := by linarith,

  cases hsf m hm_gt_Mf with fbound_low fbound_high,
  cases hsg m hm_gt_Mg with gbound_low gbound_high,

  split,
  {
    linarith,
  },
  {
    linarith,
  }
end

-- scaling the summands scales the indefinite sum by the same amount
theorem indefinite_summation_scaling {f : ℤ → ℚ} {κ c : ℚ} : equals_indefinite_sum f c → equals_indefinite_sum (λ n, κ * (f n)) (κ * c) :=
begin
  unfold equals_indefinite_sum at *,
  intro hsumf,
  intro ε, intro hεpos,

  have h_trichotomy : κ < 0 ∨ κ = 0 ∨ κ > 0 := trichotomous κ 0,

  cases h_trichotomy,
  {
    let ε' := (-ε) / κ,
    have ε'pos : ε' > 0 := div_pos_of_neg_of_neg (neg_lt_zero.mpr hεpos) h_trichotomy,
    
    cases hsumf ε' ε'pos with M hM,
    
    use M,

    intro m, intro hmgtM,

    have h : ε = -κ * ε' := by {
      have g : ε' * κ = (-ε) := (eq_div_iff (ne_of_lt h_trichotomy)).mp rfl,
      linarith,
    },

    rw h at *,
    rw summation_scaling at *,
    split,
    {
      have hs : _ := (hM m hmgtM).2,
      have hm : _ := mul_lt_mul_of_neg_left hs h_trichotomy,
      ring_nf,
      rw mul_add at hm,
      linarith,
    },
    {
      have hs : _ := (hM m hmgtM).1,
      have hm : _ := mul_lt_mul_of_neg_left hs h_trichotomy,
      ring_nf,
      rw mul_sub at hm,
      linarith,
    }        
  },
  cases h_trichotomy,
  {
    use 1,
    intro m, intro hmgt1,
    rw h_trichotomy at *,
    rw summation_scaling at *,
    simp,
    assumption,
  },
  {
    let ε' := ε / κ,
    have ε'pos : ε' > 0 := div_pos hεpos h_trichotomy,
    
    cases hsumf ε' ε'pos with M hM,
    
    use M,

    intro m, intro hmgtM,

    have h : ε = κ * ε' := by {
      rw mul_comm,
      apply eq.symm,
      exact (eq_div_iff (ne_of_gt h_trichotomy)).mp rfl,
    },

    rw h at *,
    rw summation_scaling at *,
    split,
    {
      have hs : _ := (hM m hmgtM).1,
      have hm : _ := (mul_lt_mul_left h_trichotomy).2 hs,
      rw mul_sub at hm,
      linarith,
    },
    {
      have hs : _ := (hM m hmgtM).2,
      have hm : _ := (mul_lt_mul_left h_trichotomy).2 hs,
      rw mul_add at hm,
      linarith,
    }
  }
end

-- If ∑ₖ (F (n+1) k - F n k) = 0, then ∑ₖ F n k = c  ↔  ∑ₖ F (n+1) k = c
lemma zero_diff_iff_equal (F : ℤ → ℤ → ℚ) (consecutive_difference_vanishes : ∀ (n : ℤ), equals_indefinite_sum (λ (k : ℤ), F (n+1) k - F n k) 0) (c : ℚ) : ∀ (n : ℤ), equals_indefinite_sum (F n) c ↔ equals_indefinite_sum (F (n+1)) c :=
begin
  intro n,
  split,
  {
    intro sumn,
    have h : _ := indefinite_summation_split sumn (consecutive_difference_vanishes n),
    rw add_zero at h,

    have func_equiv : (λ (k : ℤ), F n k + (F (n + 1) k - F n k)) = F (n+1) :=
    begin
      refine funext _,
      ring_nf,
      intro x,
      refl,
    end,

    rw func_equiv at h,
    exact h,
  },
  {
    intro sumns,
    have h : _ := indefinite_difference_split sumns (consecutive_difference_vanishes n),
    rw sub_zero at h,

    have func_equiv : (λ (k : ℤ), F (n+1) k - (F (n + 1) k - F n k)) = F n :=
    begin
      refine funext _,
      ring_nf,
      intro x,
      refl,
    end,
    
    rw func_equiv at h,
    exact h,
  }
end

end summation