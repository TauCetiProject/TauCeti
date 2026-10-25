/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Fricke.Normalized
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.BadPrime.Basic
import Mathlib.Algebra.Field.ZMod
import TauCeti.Data.ZMod.FinEquiv
import TauCeti.NumberTheory.ModularForms.Fricke.CharacterSpace

/-!
# `U_p 𝒲_N U_p` when the nebentypus is not defined modulo `N / p`

Let `p` be a prime dividing the level `N`, and let `χ` be a character modulo `N` that is not
defined modulo `N / p`: it is not of the form `χ₀ ∘ (ZMod N → ZMod (N / p))`. Equivalently, the
`p`-part of the conductor of `χ` is the full `p`-part of `N`. On `S_k(N, χ)`, the bad-prime
operator `U_p` and the Fricke operator `𝒲_N` then satisfy

`U_p ∘ 𝒲_N ∘ U_p = p ^ (k - 1) • 𝒲_N`.

The computation is one of matrices. Write `M = N / p` and `W = !![0, -1; N, 0]`. The `U_p`
representatives `α_b = !![1, b; 0, p]` satisfy

`α_b W α_{b'} = p · W · !![1, b'; -b M, 1 - b M b']`,

and `!![1, b'; c M, c M b' + 1]` is `T^{b'}` when `c = 0`. So `U_p (𝒲_N (U_p f))` is
`p ^ (k - 2)` times the sum of `g ∣[k] !![1, b'; c M, c M b' + 1]` over `c, b'` modulo `p`, where
`g = 𝒲_N f`. The terms with `c = 0` give `p · g`. The terms with `c ≠ 0` cancel: `g` has
nebentypus `χ⁻¹`, and an element `γ ∈ Γ₀(N)` whose lower-right entry `d` is `1` modulo `M` permutes
their `Γ₁(N)`-cosets, while it multiplies `g` by `χ(d)⁻¹`. Such a `d` with `χ(d) ≠ 1` exists exactly
because `χ` is not defined modulo `M`.

Applied to a newform, the identity gives the absolute value of its bad-prime eigenvalue in this
case (`TauCeti/NumberTheory/ModularForms/Newforms/BadPrime/Ramified.lean`).

## Main results

* `HeckeRing.GL2.heckeUCuspNat_normalizedFrickeOperatorCusp_heckeUCuspNat`:
  `U_p (𝒲_N (U_p f)) = p ^ (k - 1) • 𝒲_N f` for `f ∈ S_k(N, χ)` with `χ` not defined modulo
  `N / p`.

## References

* W.-C. W. Li, *Newforms and functional equations*, Math. Ann. **212** (1975), 285–315,
  Theorem 3.
* A. P. Ogg, *On the eigenvalues of Hecke operators*, Math. Ann. **179** (1969), 101–108.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.17.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup TauCeti

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N p : ℕ} {k : ℤ}

/-- The matrix `!![1, b; c M, c M b + 1] = !![1, 0; c M, 1] * !![1, b; 0, 1]` of `SL(2, ℤ)`. -/
private def lowerShear (M : ℕ) (c b : ℤ) : SL(2, ℤ) :=
  ⟨!![1, b; c * M, c * M * b + 1], by rw [Matrix.det_fin_two_of]; ring⟩

/-- The entries of `lowerShear M c b`. -/
private lemma coe_lowerShear (M : ℕ) (c b : ℤ) :
    (lowerShear M c b : Matrix (Fin 2) (Fin 2) ℤ) = !![1, b; c * M, c * M * b + 1] := (rfl)

/-- The lower-left entry of `lowerShear M c b` is `c M`. -/
private lemma lowerShear_one_zero (M : ℕ) (c b : ℤ) : lowerShear M c b 1 0 = c * M := (rfl)

/-- The lower-right entry of `lowerShear M c b` is `c M b + 1`. -/
private lemma lowerShear_one_one (M : ℕ) (c b : ℤ) :
    lowerShear M c b 1 1 = c * M * b + 1 := (rfl)

/-- A function with nebentypus `ψ` for `Γ₀(N)` is invariant under `Γ₁(N)`. -/
private lemma slash_mapGL_eq_self_of_mem_Gamma1 {G : ℍ → ℂ} {ψ : (ZMod N)ˣ →* ℂˣ}
    (hG : ∀ g : ↥(Gamma0 N),
      G ∣[k] mapGL ℝ (g : SL(2, ℤ)) = (ψ ((Gamma0Map N).toHomUnits g) : ℂ) • G)
    {κ : SL(2, ℤ)} (hκ : κ ∈ Gamma1 N) : G ∣[k] mapGL ℝ κ = G := by
  have h := hG ⟨κ, Gamma1_in_Gamma0 N hκ⟩
  rwa [(mem_Gamma1_iff_toHomUnits_eq_one _).mp hκ, map_one, Units.val_one, one_smul] at h

/-- A function with nebentypus `ψ` for `Γ₀(N)` has the same slash by two matrices whose lower
rows agree modulo `N`, since these lie in one right coset of `Γ₁(N)`. -/
private lemma slash_mapGL_eq_of_dvd_sub {G : ℍ → ℂ} {ψ : (ZMod N)ˣ →* ℂˣ}
    (hG : ∀ g : ↥(Gamma0 N),
      G ∣[k] mapGL ℝ (g : SL(2, ℤ)) = (ψ ((Gamma0Map N).toHomUnits g) : ℂ) • G)
    {A B : SL(2, ℤ)} (h10 : (N : ℤ) ∣ A 1 0 - B 1 0) (h11 : (N : ℤ) ∣ A 1 1 - B 1 1) :
    G ∣[k] mapGL ℝ A = G ∣[k] mapGL ℝ B := by
  conv_lhs => rw [← inv_mul_cancel_right A B]
  rw [map_mul, SlashAction.slash_mul, slash_mapGL_eq_self_of_mem_Gamma1 hG
    (mul_inv_mem_Gamma1_iff_dvd_sub.mpr ⟨h10, h11⟩)]

/-- The slash by `lowerShear M c b` depends only on `c` and `b` modulo `p`, where `M = N / p`. -/
private lemma slash_lowerShear_congr {G : ℍ → ℂ} {ψ : (ZMod N)ˣ →* ℂˣ}
    (hG : ∀ g : ↥(Gamma0 N),
      G ∣[k] mapGL ℝ (g : SL(2, ℤ)) = (ψ ((Gamma0Map N).toHomUnits g) : ℂ) • G)
    (hpN : p ∣ N) {c₁ c₂ b₁ b₂ : ℤ} (hc : (c₁ : ZMod p) = c₂) (hb : (b₁ : ZMod p) = b₂) :
    G ∣[k] mapGL ℝ (lowerShear (N / p) c₁ b₁) = G ∣[k] mapGL ℝ (lowerShear (N / p) c₂ b₂) := by
  have hMp : ((N / p : ℕ) : ℤ) * p = N := by exact_mod_cast Nat.div_mul_cancel hpN
  obtain ⟨x, hx⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub c₂ c₁ p).mp hc.symm
  obtain ⟨y, hy⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (c₂ * b₂) (c₁ * b₁) p).mp
    (by push_cast; rw [hc, hb])
  refine slash_mapGL_eq_of_dvd_sub hG ⟨x, ?_⟩ ⟨y, ?_⟩
  · rw [lowerShear_one_zero, lowerShear_one_zero]
    linear_combination (N / p : ℕ) * hx + x * hMp
  · rw [lowerShear_one_one, lowerShear_one_one]
    linear_combination (N / p : ℕ) * hy + y * hMp

/-- **A matrix of `Γ₀(N)` permutes the right `Γ₁(N)`-cosets of the `lowerShear` matrices.** Let
`g ∈ Γ₀(N)` have lower-right entry `d = 1 + M t`, where `M = N / p`, and let `v` be `d` modulo `p`.
For `c ≠ 0` modulo `p`, the product `g · !![1, b; c M, c M b + 1]` has, modulo `N`, the lower row of
the same matrix at `(v c, b + t (v c)⁻¹)`. -/
private lemma slash_mul_lowerShear [Fact p.Prime] (hpN : p ∣ N) {G : ℍ → ℂ}
    {ψ : (ZMod N)ˣ →* ℂˣ}
    (hG : ∀ g : ↥(Gamma0 N),
      G ∣[k] mapGL ℝ (g : SL(2, ℤ)) = (ψ ((Gamma0Map N).toHomUnits g) : ℂ) • G)
    (g : ↥(Gamma0 N)) {t : ℤ} (ht : (g : SL(2, ℤ)) 1 1 - 1 = (N / p : ℕ) * t) {v : (ZMod p)ˣ}
    (hv : (v : ZMod p) = (g : SL(2, ℤ)) 1 1) {c : ZMod p} (hc : c ≠ 0) (b : ZMod p) :
    G ∣[k] mapGL ℝ ((g : SL(2, ℤ)) * lowerShear (N / p) c.val b.val) =
      G ∣[k] mapGL ℝ (lowerShear (N / p) ((v : ZMod p) * c).val
        (b + t * ((v : ZMod p) * c)⁻¹).val) := by
  set M := N / p
  have hMp : (M : ℤ) * p = N := by exact_mod_cast Nat.div_mul_cancel hpN
  have hvc : (v : ZMod p) * c ≠ 0 := mul_ne_zero v.ne_zero hc
  obtain ⟨z, hz⟩ : (N : ℤ) ∣ (g : SL(2, ℤ)) 1 0 := mem_Gamma0_iff_dvd.mp g.2
  -- the two congruences modulo `p` behind the lower rows
  obtain ⟨y₁, hy₁⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub ((g : SL(2, ℤ)) 1 1 * c.val)
    (((v : ZMod p) * c).val) p).mp (by push_cast; simp [hv])
  obtain ⟨y₂, hy₂⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub
    ((g : SL(2, ℤ)) 1 1 * c.val * b.val + t)
    (((v : ZMod p) * c).val * (b + t * ((v : ZMod p) * c)⁻¹).val) p).mp (by
      push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id', id, ← hv]
      field_simp)
  refine slash_mapGL_eq_of_dvd_sub hG ⟨z - y₁, ?_⟩ ⟨z * b.val - y₂, ?_⟩ <;>
    simp only [coe_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_lowerShear, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
  · linear_combination hz - (M : ℤ) * hy₁ - y₁ * hMp
  · linear_combination b.val * hz + ht - (M : ℤ) * hy₂ - y₂ * hMp

/-- **The terms with `c ≠ 0` cancel.** Let `G` have nebentypus `ψ` for `Γ₀(N)`, and let `u` be a
unit modulo `N` that is `1` modulo `M = N / p` with `ψ(u) ≠ 1`. Then the sum of the slashes of `G`
by `!![1, b; c M, c M b + 1]` over `c ≠ 0` and `b` modulo `p` vanishes: a matrix of `Γ₀(N)` with
lower-right entry `u` permutes their right `Γ₁(N)`-cosets (`slash_mul_lowerShear`) and multiplies
`G` by `ψ(u)`. -/
private lemma sum_slash_lowerShear_eq_zero [Fact p.Prime] (hpN : p ∣ N) {G : ℍ → ℂ}
    {ψ : (ZMod N)ˣ →* ℂˣ}
    (hG : ∀ g : ↥(Gamma0 N),
      G ∣[k] mapGL ℝ (g : SL(2, ℤ)) = (ψ ((Gamma0Map N).toHomUnits g) : ℂ) • G)
    {u : (ZMod N)ˣ} (hu : ZMod.unitsMap (Nat.div_dvd_of_dvd hpN) u = 1) (hψ : ψ u ≠ 1) :
    ∑ c ∈ ({0}ᶜ : Finset (ZMod p)), ∑ b : ZMod p,
      G ∣[k] mapGL ℝ (lowerShear (N / p) c.val b.val) = 0 := by
  -- a matrix `g ∈ Γ₀(N)` with lower-right entry `d ≡ u (mod N)`, so that `d = 1 + (N / p) t`
  obtain ⟨g, hg⟩ := Gamma0Map_toHomUnits_surjective (N := N) u
  have hdN : (((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = u := by
    simpa [MonoidHom.coe_toHomUnits, Gamma0Map_apply] using congrArg Units.val hg
  obtain ⟨t, ht⟩ : ((N / p : ℕ) : ℤ) ∣ (g : SL(2, ℤ)) 1 1 - 1 := by
    refine (ZMod.intCast_eq_intCast_iff_dvd_sub 1 _ (N / p)).mp ?_
    have h := congrArg Units.val hu
    rw [ZMod.unitsMap_val, ← hdN, ZMod.cast_intCast (Nat.div_dvd_of_dvd hpN)] at h
    simpa using h.symm
  set v : (ZMod p)ˣ := ZMod.unitsMap hpN u with hv
  have hvd : (v : ZMod p) = (g : SL(2, ℤ)) 1 1 := by
    rw [hv, ZMod.unitsMap_val, ← hdN, ZMod.cast_intCast hpN]
  -- the sum is fixed by multiplication by `ψ(u) ≠ 1`
  set S := ∑ c ∈ ({0}ᶜ : Finset (ZMod p)), ∑ b : ZMod p,
    G ∣[k] mapGL ℝ (lowerShear (N / p) c.val b.val) with hS
  have hfix : (ψ u : ℂ) • S = S := by
    calc (ψ u : ℂ) • S
        = ∑ c ∈ ({0}ᶜ : Finset (ZMod p)), ∑ b : ZMod p,
            G ∣[k] mapGL ℝ ((g : SL(2, ℤ)) * lowerShear (N / p) c.val b.val) := by
          rw [hS, Finset.smul_sum]
          refine Finset.sum_congr rfl fun c _ ↦ ?_
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun b _ ↦ ?_
          rw [map_mul, SlashAction.slash_mul, hG g, hg, ModularForm.smul_slash_of_det_pos k
            (det_pos_of_mem_slGL (MonoidHom.mem_range.mpr ⟨_, rfl⟩))]
      _ = ∑ c ∈ ({0}ᶜ : Finset (ZMod p)), ∑ b : ZMod p,
            G ∣[k] mapGL ℝ (lowerShear (N / p) ((v : ZMod p) * c).val b.val) := by
          refine Finset.sum_congr rfl fun c hc ↦ ?_
          have hc0 : c ≠ 0 := by simpa using hc
          exact Fintype.sum_equiv (Equiv.addRight (t * ((v : ZMod p) * c)⁻¹)) _ _
            fun b ↦ slash_mul_lowerShear hpN hG g ht hvd hc0 b
      _ = S := by
          refine Finset.sum_nbij' (fun c ↦ (v : ZMod p) * c) (fun c ↦ (v⁻¹ : (ZMod p)ˣ) * c)
            ?_ ?_ (fun c _ ↦ Units.inv_mul_cancel_left v c)
            (fun c _ ↦ Units.mul_inv_cancel_left v c) fun _ _ ↦ rfl
          · intro c hc
            rw [Finset.mem_compl, Finset.mem_singleton] at hc ⊢
            exact mul_ne_zero v.ne_zero hc
          · intro c hc
            rw [Finset.mem_compl, Finset.mem_singleton] at hc ⊢
            exact mul_ne_zero v⁻¹.ne_zero hc
  have h0 : ((ψ u : ℂ) - 1) • S = 0 := by rw [sub_smul, hfix, one_smul, sub_self]
  exact (smul_eq_zero.mp h0).resolve_left
    (sub_ne_zero.mpr fun h ↦ hψ (Units.val_eq_one.mp h))

/-- **The matrix identity** `α_b W α_{b'} = p · W · !![1, b'; -b M, 1 - b M b']` in `GL(2, ℝ)`,
where `α_b = !![1, b; 0, p]` is a `U_p` representative, `W = !![0, -1; N, 0]` and `M = N / p`. -/
private lemma map_upperTriRep_mul_frickeGL_mul_map_upperTriRep [NeZero N] [NeZero p] {M : ℕ}
    (hMp : M * p = N) (b b' : Fin p) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p b) * frickeGL ℝ N *
        Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p b') =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p : ℝ) (NeZero.ne _)) *
        (frickeGL ℝ N * mapGL ℝ (lowerShear M (-(b : ℤ)) b')) := by
  have hMp' : (M : ℝ) * p = N := by exact_mod_cast hMp
  ext i j
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, coe_lowerShear,
      Matrix.GeneralLinearGroup.val_map_apply, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.vecMul, dotProduct, ← hMp'] <;> ring

/-- `U_p (U_p F ∣[k] W) = p ^ (k - 1) • (F ∣[k] W)` on functions, when `F ∣[k] W` has a
nebentypus `ψ` for `Γ₀(N)` that is not trivial on the units that are `1` modulo `N / p`. -/
private lemma heckeSlashUpperTri_slash_frickeGL_heckeSlashUpperTri [NeZero N] [Fact p.Prime]
    (hpN : p ∣ N) {F : ℍ → ℂ} {ψ : (ZMod N)ˣ →* ℂˣ}
    (hG : ∀ g : ↥(Gamma0 N), (F ∣[k] frickeGL ℝ N) ∣[k] mapGL ℝ (g : SL(2, ℤ)) =
      (ψ ((Gamma0Map N).toHomUnits g) : ℂ) • (F ∣[k] frickeGL ℝ N))
    {u : (ZMod N)ˣ} (hu : ZMod.unitsMap (Nat.div_dvd_of_dvd hpN) u = 1) (hψ : ψ u ≠ 1) :
    heckeSlashUpperTri k p (heckeSlashUpperTri k p F ∣[k] frickeGL ℝ N) =
      (p : ℂ) ^ (k - 1) • (F ∣[k] frickeGL ℝ N) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  -- each of the `p²` terms is `p ^ (k - 2)` times a slash of `F ∣[k] W`
  have hterm : ∀ b b' : Fin p, ((F ∣[k] upperTriRep p b) ∣[k] frickeGL ℝ N) ∣[k]
      upperTriRep p b' = (p : ℂ) ^ (k - 2) •
        (F ∣[k] frickeGL ℝ N) ∣[k] mapGL ℝ (lowerShear (N / p) (-(b : ℤ)) b') := by
    intro b b'
    rw [ModularForm.rat_slash, ModularForm.rat_slash, ← SlashAction.slash_mul,
      ← SlashAction.slash_mul, ← mul_assoc,
      map_upperTriRep_mul_frickeGL_mul_map_upperTriRep (Nat.div_mul_cancel hpN),
      SlashAction.slash_mul, ModularForm.slash_scalar, SlashAction.slash_mul,
      ModularForm.smul_slash_of_det_pos k val_det_frickeGL_pos,
      ModularForm.smul_slash_of_det_pos k
        (det_pos_of_mem_slGL (MonoidHom.mem_range.mpr ⟨_, rfl⟩)), Units.val_mk0,
      Complex.ofReal_natCast]
  set G := F ∣[k] frickeGL ℝ N
  -- the terms with `c = 0` are translates of `G`, hence equal to `G`
  have hzero : ∑ y : ZMod p, G ∣[k] mapGL ℝ (lowerShear (N / p) (0 : ZMod p).val y.val) =
      (p : ℂ) • G := by
    have hT : ∀ y : ZMod p, G ∣[k] mapGL ℝ (lowerShear (N / p) (0 : ZMod p).val y.val) = G :=
      fun y ↦ slash_mapGL_eq_self_of_mem_Gamma1 hG
        (mem_Gamma1_of_dvd_lowerRow (by simp [lowerShear_one_zero])
          (by simp [lowerShear_one_one]))
    rw [Finset.sum_congr rfl fun y _ ↦ hT y, Finset.sum_const, Finset.card_univ, ZMod.card,
      ← Nat.cast_smul_eq_nsmul ℂ]
  -- reindex the double sum by residues modulo `p`
  have hreindex : ∑ b : Fin p, ∑ b' : Fin p,
      G ∣[k] mapGL ℝ (lowerShear (N / p) (-(b : ℤ)) b') =
        ∑ x : ZMod p, ∑ y : ZMod p, G ∣[k] mapGL ℝ (lowerShear (N / p) x.val y.val) := by
    refine Fintype.sum_equiv ((ZMod.finEquiv p).toEquiv.trans (Equiv.neg _)) _ _ fun b ↦ ?_
    refine Fintype.sum_equiv (ZMod.finEquiv p).toEquiv _ _ fun b' ↦ ?_
    refine slash_lowerShear_congr hG hpN ?_ ?_ <;>
      simp [ZMod.finEquiv_apply]
  calc heckeSlashUpperTri k p (heckeSlashUpperTri k p F ∣[k] frickeGL ℝ N)
      = ∑ b' : Fin p, ∑ b : Fin p,
          ((F ∣[k] upperTriRep p b) ∣[k] frickeGL ℝ N) ∣[k] upperTriRep p b' := by
        rw [heckeSlashUpperTri_def, heckeSlashUpperTri_def, SlashAction.sum_slash]
        refine Finset.sum_congr rfl fun b' _ ↦ ?_
        rw [SlashAction.sum_slash]
    _ = (p : ℂ) ^ (k - 2) • ∑ b : Fin p, ∑ b' : Fin p,
          G ∣[k] mapGL ℝ (lowerShear (N / p) (-(b : ℤ)) b') := by
        rw [Finset.sum_comm, Finset.smul_sum]
        refine Finset.sum_congr rfl fun b _ ↦ ?_
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun b' _ ↦ hterm b b'
    _ = (p : ℂ) ^ (k - 1) • G := by
        rw [hreindex, Fintype.sum_eq_add_sum_compl 0, hzero,
          sum_slash_lowerShear_eq_zero hpN hG hu hψ, add_zero, smul_smul,
          ← zpow_add_one₀ hp0, show k - 2 + 1 = k - 1 by ring]

/-- **`U_p 𝒲_N U_p = p ^ (k - 1) 𝒲_N` on `S_k(N, χ)`** when the nebentypus `χ` is not defined
modulo `N / p`, for a prime `p ∣ N`. Here `U_p` is the bad-prime Hecke operator and `𝒲_N` the
normalized Fricke operator.

The hypothesis on `χ` says that the `p`-part of its conductor is the full `p`-part of `N`. It cannot
be dropped: when `p ^ 2 ∣ N` and `χ` is defined modulo `N / p`, `U_p` vanishes on the new part of
`S_k(N, χ)` (`HeckeRing.GL2.heckeUCuspNat_eq_zero_of_mem_cuspFormsNew_of_sq_dvd`), so the identity
fails at every nonzero form of that new part. -/
theorem heckeUCuspNat_normalizedFrickeOperatorCusp_heckeUCuspNat [NeZero N] (hp : p.Prime)
    (hpN : p ∣ N) {χ : (ZMod N)ˣ →* ℂˣ}
    (hχ : ¬ ∃ χ₀ : (ZMod (N / p))ˣ →* ℂˣ, χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    heckeUCuspNat k p hp hpN (normalizedFrickeOperatorCusp k (heckeUCuspNat k p hp hpN f)) =
      (p : ℂ) ^ (k - 1) • normalizedFrickeOperatorCusp k f := by
  have : Fact p.Prime := ⟨hp⟩
  -- a unit `u ≡ 1 (mod N / p)` with `χ(u) ≠ 1`: otherwise `χ` factors through `N / p`
  obtain ⟨u, hu, hχu⟩ : ∃ u : (ZMod N)ˣ,
      ZMod.unitsMap (Nat.div_dvd_of_dvd hpN) u = 1 ∧ χ u ≠ 1 := by
    by_contra! h
    have hs := ZMod.unitsMap_surjective (Nat.div_dvd_of_dvd hpN)
    exact hχ ⟨(ZMod.unitsMap _).liftOfRightInverse _ (Function.rightInverse_surjInv hs)
      ⟨χ, fun v hv ↦ h v hv⟩, (MonoidHom.liftOfRightInverse_comp (ZMod.unitsMap _) _
        (Function.rightInverse_surjInv hs) ⟨χ, fun v hv ↦ h v hv⟩).symm⟩
  -- `W f` has nebentypus `χ⁻¹`
  have hG := (mem_cuspFormCharSpace_iff_nebentypus k χ⁻¹ _).mp
    (frickeOperatorCusp_mem_cuspFormCharSpace k χ hf)
  simp only [coe_frickeOperatorCusp] at hG
  have hψ : χ⁻¹ u ≠ 1 := by
    rw [MonoidHom.inv_apply]
    exact inv_ne_one.mpr hχu
  refine DFunLike.coe_injective ?_
  rw [heckeUCuspNat_eq_heckeTCuspNat, heckeTCuspNat_eq_upperTri k hpN,
    coe_heckeSlashUpperTriCuspFormEnd, coe_normalizedFrickeOperatorCusp,
    coe_heckeSlashUpperTriCuspFormEnd, heckeSlashUpperTri_smul,
    heckeSlashUpperTri_slash_frickeGL_heckeSlashUpperTri hpN hG hu hψ, FunLike.coe_smul,
    coe_normalizedFrickeOperatorCusp, smul_comm]

end HeckeRing.GL2
