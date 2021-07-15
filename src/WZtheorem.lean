import data.rat.basic

import summation

open summation

/-The limit as `f` goes to ±∞ is 0 -/
def vanishes (f : ℤ → ℚ) := ∀ (ε : ℚ), ε > (0 : ℚ) → ∃ (K : ℕ), ∀ (k : ℤ), (k > K ∨ k < -K) → (f k > - ε ∧ f k < ε)

/-
The functions `F` and `G` form a WZ pair

That is, Δₙ F = Δₖ G
-/
def WZ_pair (F : ℕ → ℤ → ℚ) (G : ℕ → ℤ → ℚ) := (∀ (n : ℕ), ∀ (k : ℤ), F (n+1) k - F n k = G n (k+1) - G n k)

/-
This lemma demonstrates that if functions `F` and `G` form a WZ pair, then a finite summation of `F` with the variable `k` can be converted to a telescoping sum of the funtion `G`.
-/
lemma creative_telescoping {F G : ℕ → ℤ → ℚ} (wz : WZ_pair F G) (n : ℕ) : ∀ (m : ℕ), summation (λ (k : ℤ), F (n+1) k - F n k) m = G n (m+1) - G n (-m) :=
begin
  intro m,
  induction m with d hd,
  {
    rw [summation, wz n 0],
    refl,
  },
  {
    rw [summation, hd, wz, wz],
    simp,
  }
end

/-This is the main WZ theorem.

Sketch of the proof:

Any identity of the form ∑ₖ f n k = S n can be rewritten as
∑ₖ F n k = c, where
`c` is a constant and
F n k = (f n k) / (S n)

To show that ∑ₖ F n k = c, it suffices to show that (∑ₖ F (n+1) k) - (∑ₖ F n k) = ∑ₖ (F (n+1) k - F n k) = 0.

Using the WZ mate of `F`, namely `G`, this summation can be converted into a telescoping sum which is easily evaluated:

∑ₖ G n (k+1) - G n k = lim_{m → ∞} G n (m+1) - G n (-m)

Since the function G n is assumed to vanish at infinity, the above sum is just zero.

This shows that ∑ₖ F n k is a constant function of `n`, and therefore the identity must hold.

-/
theorem WZ 
  (F G : ℕ → ℤ → ℚ)
  (wz : WZ_pair F G) 
  (Gvanishes : ∀ (n : ℕ), vanishes (G n)) 
  (c : ℚ)
  (base_case : equals_indefinite_sum (F 0) c)

  : ∀ (n : ℕ), equals_indefinite_sum (F n) c :=
begin

  -- this is the crux of the theorem - the fact that ∑ₖ (F (n+1) k - F n k) = 0
  have consecutive_difference_vanishes : ∀ (n : ℕ), equals_indefinite_sum (λ (k : ℤ), F (n+1) k - F n k) 0 :=
  begin
    intro n,
    rw equals_indefinite_sum,
    intros ε hε_pos,
    have hεby2_pos : ε/2 > 0 := half_pos hε_pos,
    cases (Gvanishes n (ε/2) hεby2_pos) with K hK,
    use K,
    intro m,
    intro hmgtK,
    rw creative_telescoping wz n,

    cases hK (-m) _ with Gnm_neg Gnm_pos,
    cases hK (m+1) (or.inl (int.coe_nat_lt.mpr (nat.lt.step hmgtK))) with Gnms_neg Gnms_pos,

    split,
    {
      linarith,
    },
    {
      linarith,
    },
    right,
    linarith,
  end,

  have inductive_case : _ := zero_diff_iff_equal F consecutive_difference_vanishes c,

  intro n,
  induction n with d hd,
  exact base_case,
  exact (inductive_case d).1 hd,
end