/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg
public import TauCeti.LinearAlgebra.Alternating.BaseChange

/-!
# Extension of scalars for the Chevalley–Eilenberg complex

Let `L` be a Lie algebra over a commutative ring `R`, `M` an `L`-module and `A` a commutative
`R`-algebra. Then `A ⊗[R] L` is a Lie algebra over `A` acting on `A ⊗[R] M`
(`LieAlgebra.ExtendScalars`). Extension of scalars of alternating maps
(`AlternatingMap.baseChange`) sends Chevalley–Eilenberg cochains of `L` with coefficients in `M`
to cochains of `A ⊗[R] L` with coefficients in `A ⊗[R] M`, and it commutes with the
Chevalley–Eilenberg differential (`TauCeti.LieModule.Cohomology.d_baseChange`). The proof is an
induction through Cartan's formula `ι_x d ω = ⁅x, ω⁆ - d ι_x ω`, using that extension of scalars
intertwines the Lie derivatives (`AlternatingMap.lie_baseChange`) and the interior products along
the tensors `1 ⊗ₜ x`.

When `L` is finite free over `R` (for instance finite-dimensional over a field), extension of
scalars of cochains is an isomorphism `A ⊗[R] C^n(L, M) ≅ C^n(A ⊗[R] L, A ⊗[R] M)` in each degree
(`AlternatingMap.baseChangeEquiv`). These assemble into an isomorphism between the extension of
scalars of the Chevalley–Eilenberg complex, computed degreewise by `ModuleCat.extendScalars`, and
the Chevalley–Eilenberg complex of the extended Lie algebra
(`TauCeti.LieModule.Cohomology.cochainComplexBaseChangeIso`):
`C^•(𝔤, V) ⊗_E E′ ≅ C^•(𝔤 ⊗_E E′, V ⊗_E E′)` for a finite-dimensional Lie algebra `𝔤` over a field
`E` and a field extension `E′/E`. This compares, for instance, the cohomology of a real Lie algebra
with that of its complexification.

## Main results

* `AlternatingMap.lie_baseChange`: `⁅1 ⊗ₜ x, f.baseChange A⁆ = ⁅x, f⁆.baseChange A`.
* `TauCeti.LieModule.Cohomology.d_baseChange`: the differential commutes with extension of
  scalars of cochains.
* `TauCeti.LieModule.Cohomology.cochainsBaseChangeIso`: the degreewise isomorphism, from the
  extension of scalars of the module of cochains.
* `TauCeti.LieModule.Cohomology.cochainComplexBaseChangeIso`: the isomorphism of cochain
  complexes.

## References

* C. Chevalley and S. Eilenberg, *Cohomology theory of Lie groups and Lie algebras*,
  Trans. Amer. Math. Soc. 63 (1948), 85–124.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  §7.7.
-/

public section

open CategoryTheory TensorProduct

namespace AlternatingMap

variable {R : Type*} (A : Type*) {L M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

/-- The action of `1 ⊗ₜ x` on the extension of scalars of an alternating map is the extension of
scalars of the action of `x`. -/
@[simp]
theorem lie_baseChange {n : ℕ} (x : L) (f : M [⋀^Fin n]→ₗ[R] N) :
    ⁅(1 : A) ⊗ₜ[R] x, f.baseChange A⁆ = ⁅x, f⁆.baseChange A := by
  refine baseChange_ext A fun m ↦ ?_
  have hupd (i : Fin n) : Function.update (fun k ↦ (1 : A) ⊗ₜ[R] m k) i (1 ⊗ₜ ⁅x, m i⁆) =
      fun k ↦ 1 ⊗ₜ Function.update m i ⁅x, m i⁆ k := by
    ext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  simp [hupd, tmul_sub, tmul_sum]

end AlternatingMap

namespace TauCeti.LieModule.Cohomology

section Differential

variable (R : Type*) (A : Type*) {L M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The Chevalley–Eilenberg differential commutes with extension of scalars of cochains. -/
@[simp]
theorem d_baseChange (n : ℕ) (ω : L [⋀^Fin n]→ₗ[R] M) :
    d A (A ⊗[R] L) (A ⊗[R] M) n (ω.baseChange A) = (d R L M n ω).baseChange A := by
  -- Compare interior products with the tensors `1 ⊗ₜ x` through Cartan's formula.
  induction n with
  | zero =>
    refine AlternatingMap.baseChange_ext_curryLeft A fun x ↦ ?_
    simp
  | succ n ih =>
    refine AlternatingMap.baseChange_ext_curryLeft A fun x ↦ ?_
    simp [ih]

variable {R A}
variable [Module.Free R L] [Module.Finite R L]

/-- For finite free `L`, the comparison `AlternatingMap.baseChangeEquiv` of cochain modules
intertwines the extension of scalars of the differential with the differential of the extended
Lie algebra. -/
theorem baseChangeEquiv_baseChange_d (n : ℕ) (c : A ⊗[R] (L [⋀^Fin n]→ₗ[R] M)) :
    AlternatingMap.baseChangeEquiv R A L M (n + 1) ((d R L M n).baseChange A c) =
      d A (A ⊗[R] L) (A ⊗[R] M) n (AlternatingMap.baseChangeEquiv R A L M n c) := by
  induction c using TensorProduct.inductionOn with
  | tmul a ω => simp [d_baseChange]
  | add x y hx hy => simp [hx, hy]

end Differential

section Complex

variable (R A L M : Type*) [CommRing R] [CommRing A] [Algebra R A]

section Cochains

variable [AddCommGroup L] [Module R L] [Module.Free R L] [Module.Finite R L]
  [AddCommGroup M] [Module R M]

/-- For finite free `L`, the extension of scalars `ModuleCat.extendScalars` of the module of
`n`-cochains `L [⋀^Fin n]→ₗ[R] M` is the module of `n`-cochains of `A ⊗[R] L` with values in
`A ⊗[R] M`, through `AlternatingMap.baseChangeEquiv`. -/
noncomputable def cochainsBaseChangeIso (n : ℕ) :
    (ModuleCat.extendScalars (algebraMap R A)).obj (ModuleCat.of R (L [⋀^Fin n]→ₗ[R] M)) ≅
      ModuleCat.of A ((A ⊗[R] L) [⋀^Fin n]→ₗ[A] (A ⊗[R] M)) :=
  ModuleCat.extendScalarsAlgebraMapIso _ ≪≫ (AlternatingMap.baseChangeEquiv R A L M n).toModuleIso

open scoped ChangeOfRings in
/-- The comparison `cochainsBaseChangeIso` sends `a ⊗ ω` to `a • ω.baseChange A`. -/
@[simp]
theorem cochainsBaseChangeIso_hom_tmul (n : ℕ) (a : A) (ω : L [⋀^Fin n]→ₗ[R] M) :
    (cochainsBaseChangeIso R A L M n).hom (a ⊗ₜ[R, algebraMap R A] ω) = a • ω.baseChange A := by
  -- The source `a ⊗ₜ ω` is typed only up to unfolding `restrictScalars`, so `simp` and forward
  -- rewrites cannot match it; rewrite the type-correct right-hand side instead.
  rw [← AlternatingMap.baseChangeEquiv_tmul, ← ModuleCat.extendScalarsAlgebraMapIso_hom_tmul
    (S := A) (ModuleCat.of R (L [⋀^Fin n]→ₗ[R] M)) a ω, cochainsBaseChangeIso, Iso.trans_hom]
  exact ModuleCat.comp_apply _ _ _

end Cochains

variable [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M] [LieRingModule L M]
  [LieModule R L M] [Module.Free R L] [Module.Finite R L]

open scoped ChangeOfRings in
/-- The degreewise comparisons `cochainsBaseChangeIso` commute with the differentials. -/
@[reassoc]
theorem extendScalars_map_d_comp_cochainsBaseChangeIso_hom (n : ℕ) :
    (ModuleCat.extendScalars (algebraMap R A)).map (ModuleCat.ofHom (d R L M n)) ≫
        (cochainsBaseChangeIso R A L M (n + 1)).hom =
      (cochainsBaseChangeIso R A L M n).hom ≫ ModuleCat.ofHom (d A (A ⊗[R] L) (A ⊗[R] M) n) := by
  refine ModuleCat.ExtendScalars.hom_ext fun ω ↦ ?_
  -- Evaluate both composites at `1 ⊗ ω`, using `ExtendScalars.map_tmul` (true by definition).
  change (cochainsBaseChangeIso R A L M (n + 1)).hom ((1 : A) ⊗ₜ[R, algebraMap R A] d R L M n ω) =
    d A (A ⊗[R] L) (A ⊗[R] M) n
      ((cochainsBaseChangeIso R A L M n).hom ((1 : A) ⊗ₜ[R, algebraMap R A] ω))
  rw [cochainsBaseChangeIso_hom_tmul, cochainsBaseChangeIso_hom_tmul]
  simp

/-- **Extension of scalars of the Chevalley–Eilenberg complex.** For a Lie algebra `L` that is
finite free over `R`, the extension of scalars of the Chevalley–Eilenberg complex of `L` with
coefficients in `M` is isomorphic to the Chevalley–Eilenberg complex of `A ⊗[R] L` with
coefficients in `A ⊗[R] M`. -/
noncomputable def cochainComplexBaseChangeIso :
    ((ModuleCat.extendScalars (algebraMap R A)).mapHomologicalComplex _).obj
        (cochainComplex R L M) ≅
      cochainComplex A (A ⊗[R] L) (A ⊗[R] M) :=
  HomologicalComplex.Hom.isoOfComponents (cochainsBaseChangeIso R A L M) (by
    rintro i j (rfl : i + 1 = j)
    simp only [Functor.mapHomologicalComplex_obj_d, cochainComplex_d_succ]
    exact (extendScalars_map_d_comp_cochainsBaseChangeIso_hom R A L M i).symm)

/-- In degree `n`, `cochainComplexBaseChangeIso` is `cochainsBaseChangeIso`. -/
@[simp]
theorem cochainComplexBaseChangeIso_hom_f (n : ℕ) :
    (cochainComplexBaseChangeIso R A L M).hom.f n = (cochainsBaseChangeIso R A L M n).hom :=
  (rfl)

/-- In degree `n`, the inverse of `cochainComplexBaseChangeIso` is that of
`cochainsBaseChangeIso`. -/
@[simp]
theorem cochainComplexBaseChangeIso_inv_f (n : ℕ) :
    (cochainComplexBaseChangeIso R A L M).inv.f n = (cochainsBaseChangeIso R A L M n).inv :=
  (rfl)

end Complex

end TauCeti.LieModule.Cohomology
