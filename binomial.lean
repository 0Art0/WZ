import tactic

namespace binomial

def binomial : ℕ → ℕ → ℕ 
  | _ 0 := 1
  | 0 _ := 0
  | (n+1) (k+1) := binomial n (k+1) + binomial n k

@[simp] lemma choose_zero_is_one (n : ℕ) : binomial n 0 = 1 := by {
  induction n with d hd,
  {
    refl,
  },
  {
    refl,
  }
}

@[simp] lemma zero_choose_succ_is_zero (n : ℕ) : binomial 0 (n+1) = 0 := by {cases n, refl, refl,}

@[simp] lemma pascal_identity (n : ℕ) (k : ℕ) : binomial (n+1) (k+1) = binomial n (k+1) + binomial n k := by refl

@[simp] lemma choose_one_is_self (n : ℕ) : binomial n 1 = n := 
begin
  induction n with d hd,
  refl,
  rw binomial,
  rw hd,
  simp,
end

@[simp] lemma n_choose_gt_n_is_zero (n : ℕ) : ∀ (k : ℕ), n < k → binomial n k = 0 := by {
  induction n with d hd,
  {
    intro k,
    intro hkpos,
    cases k,
    {
      have f : false := nat.lt_asymm hkpos hkpos,
      exact false.rec (binomial 0 0 = 0) f,
    },
    refl,
  },
  {
    intro k,
    cases k,
    {
      intro h,
      have f : false := nat.not_lt_zero d.succ h,
      exact false.rec (binomial (nat.succ d) 0 = 0) f,
    },
    {
      rw binomial,
      intro hdsks,
      have hdk : d < k := nat.succ_lt_succ_iff.mp hdsks,
      have hdks : d < k.succ := nat.lt.step hdk,
      rw hd k hdk,
      rw hd _ hdks,
    }
  }
}

@[simp] lemma choose_self_is_one (n : ℕ) : binomial n n = 1 :=
begin
  induction n with d hd,
  refl,
  rw binomial,
  rw hd,
  simp,
end

@[simp] lemma choose_succ_equals_succ (n : ℕ) : binomial n.succ n = n.succ := by {
  induction n with d hd,
  simp,
  rw binomial,
  rw hd,
  simp,
  exact (nat.succ d).one_add,
}

@[simp] lemma choose_lt_zero_is_zero (n : ℕ) : ∀ (k : ℕ), k < 0 → binomial n k = 0 := by {
  induction n with d hd,
  {
    intro k,
    intro hkltzero,
    cases k,
    {
      have f : false := nat.lt_asymm hkltzero hkltzero,
      exact false.rec (binomial 0 0 = 0) f,
    },
    refl,
  },
  {
    intro k,
    intro hkltzero,
    cases k,
    {
      have f : false := nat.lt_asymm hkltzero hkltzero,
      exact false.rec (binomial (nat.succ d) 0 = 0) f,
    },
    {
      rw binomial,
      have hk_ltzero : k < 0 := nat.lt_of_succ_lt hkltzero,
      rw hd _ hk_ltzero,
      rw hd _ hkltzero,
    }
  }
}

lemma choose_pos (n : ℕ) : ∀ {k : ℕ}, k ≤ n → 0 < binomial n k := by {
  induction n with d hd,
  {
    intro k,
    intro kzero,
    cases k,
    {
      simp,
    },
    {
      simp,
      exact nat.not_succ_le_zero k kzero,
    },
  },
  {
    intro k,
    intro hkltds,
    cases k,
    {
      simp,
    },
    {
      rw binomial,
      have hkld : k ≤ d := nat.succ_le_succ_iff.mp hkltds,
      have hbindkpos : 0 < binomial d k := hd hkld,
      linarith,
    }
  }
}

lemma pascal_identity_with_conditions (n : ℕ) (k : ℕ) : (0 < k) → binomial n k + binomial n (k-1) = binomial n.succ k :=
begin
  intro hkpos,
  have h_pred : ∃ (m : ℕ), k = m.succ :=
  begin
    refine nat.exists_eq_succ_of_ne_zero _,
    linarith,
  end,
  cases h_pred with m hm,
  rw hm at *,
  rw pascal_identity,
  simp,
end

theorem binomial_symm (n : ℕ) : ∀ (k : ℕ), k ≤ n → binomial n k = binomial n (n - k) := 
begin
  induction n with d hd,
  {
    intro k,
    intro hkleqzero,
    cases k,
    {
      refl,
    },
    {
      have f : false := nat.not_succ_le_zero k hkleqzero,
      exact congr_arg (binomial 0) (congr_fun (false.rec (nat.succ = λ (k : ℕ), 0 - k.succ) f) k),
    }
  },
  {
    intro k,
    intro hkleqds,
    cases k,
    {
      simp,
    },
    {
      rw binomial,
      have hkld : k ≤ d := nat.succ_le_succ_iff.mp hkleqds,
      rw hd _ hkld,
      cases hkleqds,
      {
        simp,
      },
      {
        rw hd _ hkleqds_ᾰ,
        rw add_comm,
        have hdks : (d - k.succ) = ((d - k) - 1) := by {
          rw nat.succ_eq_add_one,
          exact (nat.sub_sub d k 1).symm,
        },
        rw hdks,
        have dk_succ_diff : d.succ - k.succ = d - k := nat.succ_sub_succ d k,
        rw dk_succ_diff,
        have hksleqd : k + 1 ≤ d := hkleqds_ᾰ,
        have dk_diff_pos : 0 < d-k := by {
          refine nat.succ_le_iff.mp _,
          exact nat.le_sub_left_of_add_le hksleqd,
        },
        exact pascal_identity_with_conditions d (d-k) dk_diff_pos,
      }
    }
  }
end

end binomial