/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Tor

import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.LinearAlgebra.TensorProduct.Projective
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.CategoryTheory.Abelian.Projective.Dimension

/-!
# Projective dimension under `Tor`-acyclic base change and homological epimorphisms

For a commutative `R`-algebra `S` and an `R`-module `M`, flat base change satisfies
`pd_S (S ⊗[R] M) ≤ pd_R M` (`ModuleCat.projectiveDimension_tensorProduct_le`). Flatness of `S`
over `R` is only used to keep projective presentations exact after tensoring with `S`, so for a
fixed module `M` of projective dimension at most `d` it suffices that `Tor_{i+1}^R(M, S) = 0` for
`i < d` (`ModuleCat.hasProjectiveDimensionLE_tensorProduct_of_isZero_Tor`): along a projective
presentation `0 → K → P → M → 0`, vanishing of `Tor₁^R(M, S)` makes `0 → S ⊗[R] K → S ⊗[R] P →
S ⊗[R] M → 0` exact, while vanishing of the higher `Tor` groups shifts to `K`.

Both hypotheses must hold in general: over `R = k[x] ⧸ (x ^ 2)` and `S = k`, the module `M = k` has
`Tor_i^R(k, k) ≠ 0` while `S ⊗[R] M = k` is projective; conversely, over `R = ℤ` and `S = ℤ ⧸ 4ℤ`,
the module `M = ℤ ⧸ 2ℤ` has projective dimension `1` over `ℤ`, `Tor₁^ℤ(ℤ ⧸ 2ℤ, ℤ ⧸ 4ℤ) ≠ 0`, and
`S ⊗[ℤ] M ≃ ℤ ⧸ 2ℤ` has infinite projective dimension over `ℤ ⧸ 4ℤ`.

Combining this base-change bound with the homological epimorphism criterion for `Tor`
(`ModuleCat.isZero_Tor_succ_restrictScalars`) transports projective dimension bounds forward along
any ring homomorphism `f : A →+* B` whose restriction of scalars is full, such as a surjection or a
localization: if `Tor_{i+1}^A(B, B) = 0` for `i < d`, then every `B`-module `M` has
`B ⊗[A] M ≃ M` and `Tor_{i+1}^A(M, B) = 0` for `i < d`, so `pd_B M ≤ pd_A M` when `pd_A M ≤ d`
(`ModuleCat.hasProjectiveDimensionLE_of_restrictScalars`,
`ModuleCat.projectiveDimension_le_restrictScalars`).

## Main results

* `ModuleCat.hasProjectiveDimensionLE_tensorProduct_of_isZero_Tor`,
  `ModuleCat.hasProjectiveDimensionLT_tensorProduct_of_isZero_Tor`,
  `ModuleCat.projectiveDimension_tensorProduct_le_of_isZero_Tor`: `Tor`-acyclic base change does
  not increase projective dimension.
* `ModuleCat.hasProjectiveDimensionLT_of_restrictScalars`,
  `ModuleCat.hasProjectiveDimensionLE_of_restrictScalars`,
  `ModuleCat.projectiveDimension_le_restrictScalars`: projective dimension bounds descend from
  restriction of scalars along a homological epimorphism of commutative rings.

## References

* W. Geigle and H. Lenzing, *Perpendicular categories with applications to representations and
  sheaves*, J. Algebra 144 (1991), Proposition 4.4.
* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), proof of Proposition 11.31.
-/

public section

universe u

open CategoryTheory Limits
open scoped TensorProduct

namespace ModuleCat

section TensorProduct

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]

/-- For a surjection `f : P → M` with `Tor₁^R(M, S) = 0`, tensoring with `S` identifies
`S ⊗[R] ker f` with `ker (1_S ⊗ f)` in `ModuleCat S`. -/
private noncomputable def tensorKerIsoOfIsZeroTorOne {P M : Type u} [AddCommGroup P] [Module R P]
    [AddCommGroup M] [Module R M] {f : P →ₗ[R] M} (hf : Function.Surjective f)
    (hTor : IsZero (((Tor (ModuleCat.{u} R) 1).obj (of R M)).obj (of R S))) :
    of S (S ⊗[R] LinearMap.ker f) ≅
      of S (LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor S S f)) := by
  let ι : S ⊗[R] LinearMap.ker f →ₗ[S] S ⊗[R] P :=
    TensorProduct.AlgebraTensorModule.lTensor S S (LinearMap.ker f).subtype
  have hinj : Function.Injective ι := by
    rw [TensorProduct.AlgebraTensorModule.coe_lTensor]
    exact (LinearMap.lTensor_inj_iff_rTensor_inj S (LinearMap.ker f).subtype).mpr
      ((f.shortExact_shortComplexKer hf).rTensor_injective_of_isZero_Tor_one (of R S) hTor)
  have hex : Function.Exact ι (TensorProduct.AlgebraTensorModule.lTensor S S f) := by
    change Function.Exact ((LinearMap.ker f).subtype.lTensor S) (f.lTensor S)
    exact lTensor_exact S f.exact_subtype_ker_map hf
  let e := (LinearEquiv.ofInjective ι hinj).trans
    (LinearEquiv.ofEq _ _ (LinearMap.exact_iff.mp hex).symm)
  exact
    { hom := ofHom e.toLinearMap
      inv := ofHom e.symm.toLinearMap
      hom_inv_id := hom_ext (LinearMap.ext e.symm_apply_apply)
      inv_hom_id := hom_ext (LinearMap.ext e.apply_symm_apply) }

/-- **`Tor`-acyclic base change of projective dimension.** If `M` has projective dimension at most
`d` over `R` and `Tor_{i+1}^R(M, S) = 0` for all `i < d`, then `S ⊗[R] M` has projective dimension
at most `d` over `S`. -/
theorem hasProjectiveDimensionLE_tensorProduct_of_isZero_Tor (M : Type u) [AddCommGroup M]
    [Module R M] {d : ℕ} (h : HasProjectiveDimensionLE (of R M) d)
    (hTor : ∀ i < d, IsZero (((Tor (ModuleCat.{u} R) (i + 1)).obj (of R M)).obj (of R S))) :
    HasProjectiveDimensionLE (of S (S ⊗[R] M)) d := by
  induction d generalizing M with
  | zero =>
    rw [← projective_iff_hasProjectiveDimensionLE_zero, ← IsProjective.iff_projective] at h ⊢
    infer_instance
  | succ d ih =>
    -- Shift along the canonical projective presentation `0 → ker f → P → M → 0`.
    let P := Projective.over (of R M)
    let f := (Projective.π (of R M)).hom
    have hf : Function.Surjective f := (ModuleCat.epi_iff_surjective _).mp inferInstance
    have hS := f.shortExact_shortComplexKer hf
    rw [f.hasProjectiveDimensionLE_succ_iff_ker hf] at h
    have : Module.Flat R P := Module.Flat.of_projective
    have : HasProjectiveDimensionLE (of S (S ⊗[R] LinearMap.ker f)) d :=
      ih (LinearMap.ker f) h fun i hi ↦ hS.isZero_Tor_X₁ (of R S)
        (hTor (i + 1) (Nat.succ_lt_succ hi)) (isZero_Tor_succ_of_flat _ (of R S) i)
    have := hasProjectiveDimensionLT_of_iso
      (tensorKerIsoOfIsZeroTorOne S hf (hTor 0 d.zero_lt_succ)) (d + 1)
    exact ((TensorProduct.AlgebraTensorModule.lTensor S S f).hasProjectiveDimensionLE_succ_iff_ker
      (LinearMap.lTensor_surjective S hf) d).mpr this

/-- **`Tor`-acyclic base change of projective dimension (`<` form).** If `M` has projective
dimension less than `n` over `R` and `Tor_{i+1}^R(M, S) = 0` whenever `i + 1 < n`, then `S ⊗[R] M`
has projective dimension less than `n` over `S`. -/
theorem hasProjectiveDimensionLT_tensorProduct_of_isZero_Tor (M : Type u) [AddCommGroup M]
    [Module R M] {n : ℕ} (h : HasProjectiveDimensionLT (of R M) n)
    (hTor : ∀ i, i + 1 < n →
      IsZero (((Tor (ModuleCat.{u} R) (i + 1)).obj (of R M)).obj (of R S))) :
    HasProjectiveDimensionLT (of S (S ⊗[R] M)) n := by
  cases n with
  | zero =>
    rw [hasProjectiveDimensionLT_zero_iff_isZero, ModuleCat.isZero_iff_subsingleton] at h ⊢
    infer_instance
  | succ d =>
    exact hasProjectiveDimensionLE_tensorProduct_of_isZero_Tor S M h
      fun i hi ↦ hTor i (Nat.succ_lt_succ hi)

/-- If `Tor_{i+1}^R(M, S) = 0` for all `i`, then `pd_S (S ⊗[R] M) ≤ pd_R M`. -/
theorem projectiveDimension_tensorProduct_le_of_isZero_Tor (M : Type u) [AddCommGroup M]
    [Module R M]
    (hTor : ∀ i, IsZero (((Tor (ModuleCat.{u} R) (i + 1)).obj (of R M)).obj (of R S))) :
    projectiveDimension (of S (S ⊗[R] M)) ≤ projectiveDimension (of R M) :=
  projectiveDimension_le_of_hasProjectiveDimensionLT fun _ h ↦
    hasProjectiveDimensionLT_tensorProduct_of_isZero_Tor S M h fun i _ ↦ hTor i

end TensorProduct

section RestrictScalars

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) [(restrictScalars.{u} f).Full]

/-- **Projective dimension along a homological epimorphism (`<` form).** Let `f : A →+* B` be a
ring homomorphism whose restriction of scalars is full, for instance a surjective homomorphism or a
localization. If `M` has projective dimension less than `n` as an `A`-module and
`Tor_{i+1}^A(B, B) = 0` whenever `i + 1 < n`, then `M` has projective dimension less than `n` as a
`B`-module. -/
theorem hasProjectiveDimensionLT_of_restrictScalars (M : ModuleCat.{u} B) {n : ℕ}
    (h : HasProjectiveDimensionLT ((restrictScalars f).obj M) n)
    (hTor : ∀ i, i + 1 < n → IsZero (((Tor (ModuleCat.{u} A) (i + 1)).obj
      ((restrictScalars f).obj (of B B))).obj ((restrictScalars f).obj (of B B)))) :
    HasProjectiveDimensionLT M n := by
  let := f.toAlgebra
  let N : ModuleCat.{u} A := (restrictScalars f).obj M
  have hTorN (i : ℕ) (hi : i + 1 < n) :
      IsZero (((Tor (ModuleCat.{u} A) (i + 1)).obj N).obj (of A B)) := by
    refine IsZero.of_iso (isZero_Tor_succ_restrictScalars f M fun k hk ↦
      hTor k (Nat.lt_of_le_of_lt (Nat.succ_le_succ hk) hi)) ?_
    exact (((Tor (ModuleCat.{u} A) (i + 1)).obj N).mapIso
      (restrictScalarsAlgebraMapIso (R := A) (S := B) B).symm)
  exact @hasProjectiveDimensionLT_of_iso _ _ _ _ _
    ((extendScalarsAlgebraMapIso (R := A) (S := B) N).symm ≪≫
      asIso ((extendRestrictScalarsAdj f).counit.app M)) n
    (hasProjectiveDimensionLT_tensorProduct_of_isZero_Tor B N h hTorN)

/-- **Projective dimension along a homological epimorphism.** Let `f : A →+* B` be a ring
homomorphism whose restriction of scalars is full. If `M` has projective dimension at most `d` as
an `A`-module and `Tor_{i+1}^A(B, B) = 0` for all `i < d`, then `M` has projective dimension at
most `d` as a `B`-module. -/
theorem hasProjectiveDimensionLE_of_restrictScalars (M : ModuleCat.{u} B) {d : ℕ}
    (h : HasProjectiveDimensionLE ((restrictScalars f).obj M) d)
    (hTor : ∀ i < d, IsZero (((Tor (ModuleCat.{u} A) (i + 1)).obj
      ((restrictScalars f).obj (of B B))).obj ((restrictScalars f).obj (of B B)))) :
    HasProjectiveDimensionLE M d :=
  hasProjectiveDimensionLT_of_restrictScalars f M h fun i hi ↦ hTor i (Nat.lt_of_succ_lt_succ hi)

/-- Along a homological epimorphism `f : A →+* B`, meaning `(restrictScalars f).Full` and
`Tor_{i+1}^A(B, B) = 0` for all `i`, every `B`-module `M` satisfies `pd_B M ≤ pd_A M`. -/
theorem projectiveDimension_le_restrictScalars (M : ModuleCat.{u} B)
    (hTor : ∀ i, IsZero (((Tor (ModuleCat.{u} A) (i + 1)).obj
      ((restrictScalars f).obj (of B B))).obj ((restrictScalars f).obj (of B B)))) :
    projectiveDimension M ≤ projectiveDimension ((restrictScalars f).obj M) :=
  projectiveDimension_le_of_hasProjectiveDimensionLT fun _ h ↦
    hasProjectiveDimensionLT_of_restrictScalars f M h fun i _ ↦ hTor i

end RestrictScalars

end ModuleCat
