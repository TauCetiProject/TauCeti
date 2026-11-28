/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import TauCeti.Analysis.Complex.AppellHumbert.Positive
public import TauCeti.Analysis.Complex.AppellHumbert.Translation
import TauCeti.Analysis.Complex.AppellHumbert.Translation.CharacterSum

/-!
# Complex tori with a Hermitian action

Let `V` be a complex normed space and `L ⊆ V` an arbitrary subgroup; when `V` is finite-dimensional
and `L` is a full lattice, `V ⧸ L` is a complex torus with period lattice `L`. A **Hermitian
action** for `(V, L)` (`TauCeti.IsHermitianAction`) consists of a
commutative ring `R` with an involution `star` (a `StarRing`), a ring homomorphism
`F : R → (V →L[ℂ] V)` to the continuous complex linear endomorphisms with `F (a) L ⊆ L`, a positive
definite Hermitian form `B : V →L[ℝ] V →L[ℂ] ℂ` (continuous, real linear in the first and complex
linear in the second variable) whose Riemann form is integral on `L`, such that `F (star a)` is the
adjoint of `F (a)` for `B`, and an element `β ∈ R` with `star β = 1 - β`.

The map `b = F (β)` then satisfies `E (b u, w) + E (u, b w) = E (u, w)` for the Riemann form
`E (u, v) = Im (B (v, u) - B (u, v)) / 2π` and maps `L` into itself, so `B` with the canonical
multiplier `χ (l) = exp (πi E (l, b l))` of `b` is an Appell–Humbert datum
(`TauCeti.IsHermitianAction.appellHumbertData`), whose theta functions are the entire functions
fixed by the normalised translations `N_l`, `l ∈ L`
(`TauCeti.IsHermitianAction.mem_thetaSpace_appellHumbertData_iff`). For this datum:

* the Riemann form is positive (`TauCeti.IsHermitianAction.isPositive`) and `χ (l)² = 1` for
  `l ∈ L` (`TauCeti.IsHermitianAction.semichar_apply_sq_eq_one`); `F (star a)` is the adjoint of
  `F (a)` for it (`TauCeti.IsHermitianAction.riemannForm_apply_map`);
* for `a ∈ R`, the preimage `a⁻¹ L = {y : F (a) y ∈ L}` contains `L`, and when `V` is
  finite-dimensional and `L` is a full lattice,
  `Nat.card (a⁻¹ L ⧸ L) = |det F (a)|² = det F (a) · conj (det F (a))`: this is
  `ZLattice.natCard_quotient_comap_eq_normSq_det L (fun l hl ↦ h.map_mem a hl)` together with
  `Complex.mul_conj`. It is the index of `L` in `a⁻¹ L` when `F (a)` is invertible
  (`ZLattice.finite_quotient_comap_complex_of_det_ne_zero`); otherwise the quotient is infinite
  and both sides are `0`;
* for `f` fixed by the `N_{F (a) l}`, `l ∈ L`, and a character `ξ` of `a⁻¹ L ⧸ L`, the
  character-weighted `finsum` `s = ∑ᶠ_{k ∈ a⁻¹ L ⧸ L} ξ (-k) N_{F (a) k} f` satisfies
  `N_{F (a) y} s = ξ (y) s` for `y ∈ a⁻¹ L`, so it is an eigenvector when it is nonzero
  (`TauCeti.IsHermitianAction.normalizedTranslate_finsum_eq_smul`). The summand does not depend
  on the representative `k`.

The last fact holds for any Appell–Humbert datum, any continuous complex linear `b` with the
adjoint-half law and `E (b l, m)` integral on `L`, and any additive `A`, in place of `F (β)` and
`F (a)`
(`TauCeti.AppellHumbertData.normalizedTranslate_map_eq_of_sub_mem`,
`TauCeti.AppellHumbertData.normalizedTranslate_finsum_eq_smul`). The `finsum` is the ordinary
weighted sum when `a⁻¹ L ⧸ L` is finite, which holds when `V` is finite-dimensional, `L` is a full
lattice and `F (a)` is invertible, and it is `0` when the quotient is infinite.

Finally, for subgroups `L`, `M` of `V`, a function `q` on `M ⧸ (M ∩ L)` with
`q (x) = exp (B (x, T x))` for a biadditive `B` and an additive `T` has `(∑ᶠ q)⁴ = (∑ᶠ conj q)⁴`
(`TauCeti.finsum_pow_four_eq_finsum_conj_pow_four_of_eq_exp_form`, which needs no Hermitian
action); the
case of interest is `M = κ⁻¹ L` and `T = F (r)`.

The Riemann form here is the one of `TauCeti.AppellHumbertData`,
`E = Im (B (v, u) - B (u, v)) / 2π`, and positivity means `E (i u, u) > 0`. With the opposite
convention `E_B (u, v) = Im (B (u, v) - B (v, u)) / 2π = -E (u, v)`, the canonical multiplier
`exp (πi E_B (b x, x))` is the same function `exp (πi E (x, b x))`, and positivity
`E_B (u, i u) > 0` is the same condition.

## Main declarations

* `TauCeti.IsHermitianAction`: a Hermitian action of a ring with involution for a subgroup `L` of
  `V` (on the complex torus `V ⧸ L` when `L` is a full lattice in finite dimension).
* `TauCeti.IsHermitianAction.appellHumbertData`: its Appell–Humbert datum `(B, χ_{F (β)})`.
* `TauCeti.IsHermitianAction.isPositive`, `TauCeti.IsHermitianAction.semichar_apply_sq_eq_one`,
  `TauCeti.IsHermitianAction.riemannForm_apply_map`.
* `TauCeti.IsHermitianAction.normalizedTranslate_finsum_eq_smul`: the character-weighted `finsum`
  of translates transforms by `ξ` (an eigenvector when nonzero), a case of
  `TauCeti.AppellHumbertData.normalizedTranslate_finsum_eq_smul`.

## References

* Hermitian actions and these statements appear in `Lib/Shimura/GoodReduction/GaussSums` of the
  folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207
  (`New.ThetaTori.IsHermitianAction`, `New.ThetaTori.IsHermitianAction.isAppellHumbert`,
  `New.ThetaTori.IsHermitianAction.card_mulKernel`,
  `New.ThetaTori.IsHermitianAction.normShift_sum_eq_char_smul`,
  `New.ThetaTori.IsHermitianAction.sum_conj_pow_four_eq_sum_pow_four`).
* C. Birkenhake, H. Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Springer, 2004,
  Chapters 2 and 3 (factors of automorphy, canonical factors).
-/

public section

open Complex ComplexConjugate
open scoped Real

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {L : Submodule ℤ V}

variable {R : Type*} [CommRing R] [StarRing R]

variable (L) in
/-- A **Hermitian action** for a subgroup `L` of `V` (on the complex torus `V ⧸ L` when `V` is
finite-dimensional and `L` is a full lattice) of a commutative ring `R` with involution `star`:
a ring homomorphism `F` from `R` to the continuous complex linear endomorphisms of `V` with
`F (a) L ⊆ L`, a positive definite Hermitian form `B : V →L[ℝ] V →L[ℂ] ℂ` (continuous, real linear
in the first and complex linear in the second variable) whose Riemann form
`E (l, m) = Im (B (m, l) - B (l, m)) / 2π` is integral on `L`, such that `F (star a)` is the
adjoint of `F (a)` for `B`, and an element `β` with `star β = 1 - β`. -/
structure IsHermitianAction (F : R →+* (V →L[ℂ] V)) (B : V →L[ℝ] V →L[ℂ] ℂ) (β : R) : Prop where
  /-- Each `F (a)` maps `L` into itself. -/
  map_mem (a : R) {l : V} (hl : l ∈ L) : F a l ∈ L
  /-- `B` is Hermitian. -/
  conj_apply (u v : V) : conj (B u v) = B v u
  /-- `B` is positive definite. -/
  re_apply_self_pos {u : V} (hu : u ≠ 0) : 0 < (B u u).re
  /-- The Riemann form `Im (B (m, l) - B (l, m)) / 2π` of `B` is integral on `L`. -/
  exists_riemannForm_eq_intCast {l m : V} (hl : l ∈ L) (hm : m ∈ L) :
    ∃ n : ℤ, (B m l - B l m).im / (2 * π) = n
  /-- `F (star a)` is the adjoint of `F (a)` for `B`. -/
  apply_map (a : R) (u v : V) : B (F a u) v = B u (F (star a) v)
  /-- `star β = 1 - β`. -/
  star_eq : star β = 1 - β

namespace IsHermitianAction

variable {F : R →+* (V →L[ℂ] V)} {B : V →L[ℝ] V →L[ℂ] ℂ} {β : R}
  (h : IsHermitianAction L F B β)

include h

/-- The real part of a Hermitian form is symmetric. -/
theorem re_apply_comm (u v : V) : (B u v).re = (B v u).re := by
  rw [← h.conj_apply u v, conj_re]

/-- `B (F (β) u, w) = B (u, w) - B (u, F (β) w)`, as `F (star β) = 1 - F (β)`. -/
private theorem apply_map_beta (u w : V) : B (F β u) w = B u w - B u (F β w) := by
  rw [h.apply_map, h.star_eq, map_sub, map_one]
  -- `(1 - F β) w` is `w - F β w` by definition.
  exact map_sub (B u) w (F β w)

/-- `F (β)` is an adjoint half for the Riemann form: `E (b u, w) + E (u, b w) = E (u, w)`. -/
private theorem riemann_adj (u w : V) :
    (B w (F β u) - B (F β u) w).im / (2 * π) + (B (F β w) u - B u (F β w)).im / (2 * π) =
      (B w u - B u w).im / (2 * π) := by
  rw [h.apply_map_beta u w, h.apply_map_beta w u]
  simp only [sub_im]
  ring

/-- The Riemann form takes integer values at `(F (β) l, m)` for `l, m ∈ L`. -/
private theorem riemann_int (l m : L) :
    ∃ k : ℤ, (B m (F β l) - B (F β l) m).im / (2 * π) = k :=
  h.exists_riemannForm_eq_intCast (h.map_mem β l.property) m.property

/-- The **Appell–Humbert datum of a Hermitian action**: the form `B` with the canonical multiplier
`χ (l) = exp (πi E (l, F (β) l))` of `F (β)`
(`TauCeti.AppellHumbertData.ofCanonicalSemichar`). -/
noncomputable def appellHumbertData : AppellHumbertData L :=
  AppellHumbertData.ofCanonicalSemichar B h.re_apply_comm (F β) h.riemann_adj h.riemann_int

/-- The form of the datum of a Hermitian action is `B`. -/
@[simp]
theorem form_appellHumbertData : h.appellHumbertData.form = B :=
  AppellHumbertData.form_ofCanonicalSemichar _ _ _ _ _

/-- The semicharacter of the datum of a Hermitian action is the canonical multiplier
`χ (l) = exp (πi E (l, F (β) l))` of `F (β)`. -/
theorem semichar_appellHumbertData_apply (l : L) :
    h.appellHumbertData.semichar l =
      Circle.exp (π * h.appellHumbertData.riemannForm l (F β l)) :=
  AppellHumbertData.semichar_ofCanonicalSemichar_eq_circleExp _ _ _ _ _ l

/-- The Riemann form of the datum of a Hermitian action is that of `B`. -/
@[simp]
theorem riemannForm_appellHumbertData_apply (u v : V) :
    h.appellHumbertData.riemannForm u v = (B v u - B u v).im / (2 * π) :=
  AppellHumbertData.riemannForm_ofCanonicalSemichar_apply _ _ _ _ _ u v

/-- `F (β)` is an adjoint half for the Riemann form of the datum:
`E (F (β) u, w) + E (u, F (β) w) = E (u, w)`. -/
theorem riemannForm_apply_beta_add_eq_self (u w : V) :
    h.appellHumbertData.riemannForm (F β u) w + h.appellHumbertData.riemannForm u (F β w) =
      h.appellHumbertData.riemannForm u w := by
  simpa only [riemannForm_appellHumbertData_apply] using h.riemann_adj u w

/-- `F (star a)` is the adjoint of `F (a)` for the Riemann form of the datum:
`E (F (a) u, v) = E (u, F (star a) v)`. -/
theorem riemannForm_apply_map (a : R) (u v : V) :
    h.appellHumbertData.riemannForm (F a u) v =
      h.appellHumbertData.riemannForm u (F (star a) v) := by
  simp only [riemannForm_appellHumbertData_apply]
  -- `B (v, F (a) u) = conj (B (F (a) u, v)) = conj (B (u, F (star a) v)) = B (F (star a) v, u)`.
  rw [← h.conj_apply (F a u) v, h.apply_map, h.conj_apply]

/-- The theta functions of the datum of a Hermitian action are the entire functions fixed by the
normalised translations `N_l = χ (l)⁻¹ T_l`, `l ∈ L`. -/
theorem mem_thetaSpace_appellHumbertData_iff {f : V → ℂ} :
    f ∈ h.appellHumbertData.thetaSpace ↔ Differentiable ℂ f ∧
      ∀ l : L, h.appellHumbertData.normalizedTranslate (F β) l f = f :=
  AppellHumbertData.mem_thetaSpace_ofCanonicalSemichar_iff _ _ _ _ _

/-- **The Riemann form of a Hermitian action is positive**: `E (i u, u) = B (u, u) / π > 0` for
`u ≠ 0`. -/
theorem isPositive : h.appellHumbertData.IsPositive := by
  refine (AppellHumbertData.isPositive_iff _).mpr fun u hu ↦ ?_
  have hpos := h.re_apply_self_pos hu
  rw [riemannForm_appellHumbertData_apply, ← h.conj_apply u (I • u), (B u).map_smul, smul_eq_mul]
  simp only [sub_im, conj_im, mul_im, I_re, I_im, zero_mul, one_mul, zero_add, sub_neg_eq_add]
  positivity

/-- **The canonical multiplier of a Hermitian action squares to one** on `L`:
`χ (l)² = exp (2πi E (l, F (β) l)) = 1`. -/
@[simp]
theorem semichar_apply_sq_eq_one (l : L) : h.appellHumbertData.semichar l ^ 2 = 1 :=
  AppellHumbertData.semichar_ofCanonicalSemichar_apply_sq_eq_one _ _ _ _ _ l

/-- **The character-weighted sum of translates is an eigenvector when nonzero.** For a Hermitian
action, `a ∈ R` and `a⁻¹ L = {y : F (a) y ∈ L}`, let `f` be fixed by the normalised translations
`N_{F (a) l}`, `l ∈ L`, and `ξ` a character of `a⁻¹ L ⧸ L`. Then the character-weighted `finsum`
`s = ∑ᶠ_{z ∈ a⁻¹ L ⧸ L} ξ (-z) N_{F (a) k (z)} f`, for any choice `k (z) ∈ a⁻¹ L` of
representatives, satisfies `N_{F (a) y} s = ξ (y) s` for every `y ∈ a⁻¹ L`
(`TauCeti.AppellHumbertData.normalizedTranslate_finsum_eq_smul`). The `finsum` is the ordinary
weighted sum when `a⁻¹ L ⧸ L` is finite and `0` when it is infinite. -/
theorem normalizedTranslate_finsum_eq_smul {a : R} {f : V → ℂ}
    (hf : ∀ l ∈ L, h.appellHumbertData.normalizedTranslate (F β) (F a l) f = f)
    (ξ : AddChar (ZLattice.comap ℂ L (F a : V →ₗ[ℂ] V) ⧸
      L.submoduleOf (ZLattice.comap ℂ L (F a : V →ₗ[ℂ] V))) ℂ)
    (k : ZLattice.comap ℂ L (F a : V →ₗ[ℂ] V) ⧸
      L.submoduleOf (ZLattice.comap ℂ L (F a : V →ₗ[ℂ] V)) → ZLattice.comap ℂ L (F a : V →ₗ[ℂ] V))
    (hk : ∀ z, Submodule.Quotient.mk (k z) = z) (y : ZLattice.comap ℂ L (F a : V →ₗ[ℂ] V)) :
    h.appellHumbertData.normalizedTranslate (F β) (F a y)
        (∑ᶠ z, ξ (-z) • h.appellHumbertData.normalizedTranslate (F β) (F a (k z)) f) =
      ξ (Submodule.Quotient.mk y) •
        ∑ᶠ z, ξ (-z) • h.appellHumbertData.normalizedTranslate (F β) (F a (k z)) f :=
  -- `a⁻¹ L = ZLattice.comap ℂ L (F a)` is by definition the preimage of `L` under the underlying
  -- `ℤ`-linear map of `F a`.
  AppellHumbertData.normalizedTranslate_finsum_eq_smul (A := (F a : V →ₗ[ℂ] V).restrictScalars ℤ)
    h.riemannForm_apply_beta_add_eq_self
    (fun l m ↦ h.appellHumbertData.exists_riemannForm_eq_intCast ⟨F β l, h.map_mem β l.property⟩ m)
    hf ξ k hk y

end IsHermitianAction

end TauCeti
