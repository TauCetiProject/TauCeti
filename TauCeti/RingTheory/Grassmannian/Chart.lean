/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import TauCeti.LinearAlgebra.Finsupp.LinearCombination
public import TauCeti.RingTheory.Grassmannian.Basic
public import TauCeti.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Standard affine charts of the Grassmannian

Let `M` be a module over a commutative ring `R`. Mathlib's `Module.Grassmannian R M k`, written
`G(k, M; R)`, is the set of submodules `N ≤ M` whose quotient `M ⧸ N` is finite projective of
constant rank `k`, and `Module.Grassmannian.functor k` is the functor `A ↦ G(k, A ⊗[R] M; A)`
on commutative `R`-algebras. This file constructs the standard affine charts of this functor and
proves that each of them is represented by an explicit `R`-algebra.

For a family `x : Fin k → M`, the chart `Module.Grassmannian.chart R x` consists of those
`N ∈ G(k, M; R)` for which the images of the `x i` form a basis of `M ⧸ N`, that is, for which
`R^k → M → M ⧸ N` is bijective. Such an `N` is the kernel of a unique linear map
`φ : M → R^k` with `φ (x i) = eᵢ`, namely the inverse of `R^k ≃ M ⧸ N` composed with the
projection; conversely the kernel of any such `φ` lies in the chart
(`Module.Grassmannian.chartEquiv`). Over an `R`-algebra `A` the same applies to `A ⊗[R] M` and the
family `1 ⊗ₜ x i`, and an `A`-linear map `A ⊗[R] M → A^k` is an `R`-linear map `M → A^k`. These
are the `R`-algebra maps out of the quotient `Module.Grassmannian.ChartAlgebra R x` of the
symmetric algebra on `M^k` by the relations `φ (x i) = eᵢ`. Base change along `A → B` of the
kernel of `A ⊗[R] M → A^k` is the kernel of the base-changed map
(`Module.Grassmannian.map_ofSurjective_liftBaseChange`), so the charts over all `A` form a
subfunctor `Module.Grassmannian.chartFunctor R x` of the Grassmannian functor, corepresented by
`ChartAlgebra R x` (`Module.Grassmannian.chartHomEquiv`, natural by
`Module.Grassmannian.chartHomEquiv_comp`).

These charts are the affine pieces from which the Grassmannian scheme is glued; that the charts
are open subfunctors and that they cover the Grassmannian functor are not proved here.

## Main definitions

* `Module.Grassmannian.chart R x`: the chart of `G(k, M; R)` at `x : Fin k → M`.
* `Module.Grassmannian.chartEquiv R x`: the chart at `x` is in bijection with the linear maps
  `φ : M → R^k` with `φ (x i) = eᵢ`.
* `Module.Grassmannian.chartFunctor R x`: the chart at `x` as a subfunctor of
  `Module.Grassmannian.functor k`.
* `Module.Grassmannian.ChartAlgebra R x`: the coordinate ring of the chart at `x`.
* `Module.Grassmannian.chartHomEquiv R x A`: `R`-algebra maps `ChartAlgebra R x → A` are the
  points of the chart over `A`.

## Main results

* `Module.Grassmannian.map_ofSurjective_liftBaseChange`: base change along `A → B` sends the
  kernel of a surjection `A ⊗[R] M → A^k` to the kernel of its base change `B ⊗[R] M → B^k`.
* `Module.Grassmannian.chartHomEquiv_comp`: `chartHomEquiv` is natural in the algebra.
* `Module.Grassmannian.chartCorepresentableBy`: the chart subfunctor, on `R`-algebras in the
  universe of `ChartAlgebra R x`, is corepresented by `ChartAlgebra R x`.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7.
* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

universe u v w

open CategoryTheory TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}

section Chart

variable (R) in
/-- The chart of `G(k, M; R)` at `x : Fin k → M`: the points `N` for which the images of the
`x i` form a basis of `M ⧸ N`, that is, for which `R^k → M → M ⧸ N` is bijective. -/
def chart (x : Fin k → M) : Set G(k, M; R) :=
  {N | Function.Bijective (N.toSubmodule.mkQ ∘ₗ Fintype.linearCombination R x)}

@[simp]
theorem mem_chart_iff {x : Fin k → M} {N : G(k, M; R)} :
    N ∈ chart R x ↔ Function.Bijective (N.toSubmodule.mkQ ∘ₗ Fintype.linearCombination R x) :=
  (Iff.rfl)

/-- The kernel of a linear map `φ : M → R^k` with `φ (x i) = eᵢ` lies in the chart at `x`. -/
theorem ofSurjective_mem_chart {x : Fin k → M} {φ : M →ₗ[R] Fin k → R}
    (hφ : ∀ i, φ (x i) = Pi.single i 1) :
    ofSurjective φ (TauCeti.leftInverse_fintypeLinearCombination hφ).surjective
      (rankAtStalk_fin_fun k) ∈ chart R x := by
  set e := φ.quotKerEquivOfSurjective (TauCeti.leftInverse_fintypeLinearCombination hφ).surjective
  -- `R^k → M ⧸ ker φ` is the inverse of `M ⧸ ker φ ≃ R^k`
  have h : (LinearMap.ker φ).mkQ ∘ₗ Fintype.linearCombination R x = (e.symm : _ →ₗ[R] _) :=
    LinearMap.ext fun v ↦ e.injective <| by
      simpa [e] using TauCeti.leftInverse_fintypeLinearCombination hφ v
  rw [mem_chart_iff, toSubmodule_ofSurjective, h]
  exact LinearEquiv.bijective _

/-- The linear isomorphism `R^k ≃ M ⧸ N` for `N` in the chart at `x`. -/
noncomputable def chartQuotEquiv {x : Fin k → M} (N : chart R x) :
    (Fin k → R) ≃ₗ[R] M ⧸ N.1.toSubmodule :=
  LinearEquiv.ofBijective (N.1.toSubmodule.mkQ ∘ₗ Fintype.linearCombination R x) N.2

@[simp]
theorem chartQuotEquiv_apply {x : Fin k → M} (N : chart R x) (v : Fin k → R) :
    chartQuotEquiv N v = Submodule.Quotient.mk (Fintype.linearCombination R x v) :=
  (rfl)

variable (R) in
/-- The chart at `x` is in bijection with the linear maps `φ : M → R^k` with `φ (x i) = eᵢ`: a
point `N` corresponds to the inverse of `R^k ≃ M ⧸ N` composed with the projection, and `φ`
corresponds to its kernel. -/
noncomputable def chartEquiv (x : Fin k → M) :
    chart R x ≃ {φ : M →ₗ[R] Fin k → R // ∀ i, φ (x i) = Pi.single i 1} where
  toFun N := ⟨(chartQuotEquiv N).symm.toLinearMap ∘ₗ N.1.toSubmodule.mkQ, fun i ↦ by
    apply (chartQuotEquiv N).injective
    simp⟩
  invFun φ := ⟨_, ofSurjective_mem_chart φ.2⟩
  left_inv N := by
    ext : 2
    simp [LinearMap.ker_comp]
  right_inv φ := by
    ext m : 2
    -- `R^k ≃ M ⧸ ker φ` sends `φ m` to the class of `m`
    refine (LinearEquiv.symm_apply_eq _).2 ((Submodule.Quotient.eq _).2 (LinearMap.mem_ker.2 ?_))
    rw [map_sub, TauCeti.leftInverse_fintypeLinearCombination φ.2, sub_self]

@[simp]
theorem toSubmodule_chartEquiv_symm_apply (x : Fin k → M)
    (φ : {φ : M →ₗ[R] Fin k → R // ∀ i, φ (x i) = Pi.single i 1}) :
    ((chartEquiv R x).symm φ).1.toSubmodule = LinearMap.ker φ.1 :=
  (rfl)

@[simp]
theorem chartEquiv_apply_apply_self (x : Fin k → M) (N : chart R x) (i : Fin k) :
    (chartEquiv R x N).1 (x i) = Pi.single i 1 :=
  (chartEquiv R x N).2 i

@[simp]
theorem ker_chartEquiv_apply (x : Fin k → M) (N : chart R x) :
    LinearMap.ker (chartEquiv R x N).1 = N.1.toSubmodule := by
  rw [← toSubmodule_chartEquiv_symm_apply, Equiv.symm_apply_apply]

end Chart

section BaseChange

variable {A B : Type w} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

-- For `B` an `A`-algebra and `ψ : M → A^k` whose base change `φ : A ⊗[R] M → A^k` is surjective,
-- the map `B ⊗[R] M → B ⊗[A] ((A ⊗[R] M) ⧸ ker φ)` underlying `Grassmannian.map`, followed by
-- `B ⊗[A] ((A ⊗[R] M) ⧸ ker φ) ≃ B ⊗[A] A^k ≃ B^k`, is the base change of `M → A^k → B^k`.
private lemma piScalarRight_comp_baseChangeMkQ [Algebra A B] [IsScalarTower R A B]
    (ψ : M →ₗ[R] Fin k → A) (hψ : Function.Surjective (ψ.liftBaseChange A)) :
    (((ψ.liftBaseChange A).quotKerEquivOfSurjective hψ).baseChange A B _ _ ≪≫ₗ
        TensorProduct.piScalarRight A B B (Fin k)).toLinearMap ∘ₗ
        baseChangeMkQ B (LinearMap.ker (ψ.liftBaseChange A)) =
      ((IsScalarTower.toAlgHom R A B).toLinearMap.compLeft (Fin k) ∘ₗ ψ).liftBaseChange B := by
  ext m i
  simp [Algebra.smul_def]

/-- If the base change `A ⊗[R] M → A^k` of `ψ : M → A^k` is surjective, then so is the base change
`B ⊗[R] M → B^k` of `f ∘ ψ`, for every algebra map `f : A → B`. -/
theorem liftBaseChange_compLeft_surjective (f : A →ₐ[R] B) (ψ : M →ₗ[R] Fin k → A)
    (hψ : Function.Surjective (ψ.liftBaseChange A)) :
    Function.Surjective ((f.toLinearMap.compLeft (Fin k) ∘ₗ ψ).liftBaseChange B) := by
  algebraize [f.toRingHom]
  have hf : IsScalarTower.toAlgHom R A B = f := AlgHom.ext fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra]
  rw [← hf, ← piScalarRight_comp_baseChangeMkQ ψ hψ]
  rw [LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact (LinearEquiv.surjective _).comp (baseChangeMkQ_surjective _)

/-- Base change along an algebra map `f : A → B` sends the kernel of the surjection
`A ⊗[R] M → A^k` induced by `ψ : M → A^k` to the kernel of the surjection `B ⊗[R] M → B^k` induced
by `f ∘ ψ`. -/
theorem map_ofSurjective_liftBaseChange (f : A →ₐ[R] B) (ψ : M →ₗ[R] Fin k → A)
    (hψ : Function.Surjective (ψ.liftBaseChange A)) :
    map f (ofSurjective (ψ.liftBaseChange A) hψ (rankAtStalk_fin_fun k)) =
      ofSurjective ((f.toLinearMap.compLeft (Fin k) ∘ₗ ψ).liftBaseChange B)
        (liftBaseChange_compLeft_surjective f ψ hψ) (rankAtStalk_fin_fun k) := by
  algebraize [f.toRingHom]
  have hf : IsScalarTower.toAlgHom R A B = f := AlgHom.ext fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra]
  have h := congrArg LinearMap.ker (piScalarRight_comp_baseChangeMkQ (B := B) ψ hψ)
  rw [LinearEquiv.ker_comp, hf] at h
  ext : 1
  rw [map_toSubmodule, toSubmodule_ofSurjective, toSubmodule_ofSurjective, h]

end BaseChange

section ChartFunctor

variable (R) {A B : Type w} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- Over an `R`-algebra `A`, the chart of `G(k, A ⊗[R] M; A)` at the family `1 ⊗ₜ x i` is in
bijection with the `R`-linear maps `ψ : M → A^k` with `ψ (x i) = eᵢ`: the point attached to `ψ` is
the kernel of `A ⊗[R] M → A^k`, `a ⊗ₜ m ↦ a • ψ m`. -/
noncomputable def chartBaseChangeEquiv (A : Type w) [CommRing A] [Algebra R A] (x : Fin k → M) :
    chart A (fun i ↦ (1 : A) ⊗ₜ[R] x i) ≃
      {ψ : M →ₗ[R] Fin k → A // ∀ i, ψ (x i) = Pi.single i 1} :=
  (chartEquiv A _).trans <|
    (LinearMap.liftBaseChangeEquiv A).symm.toEquiv.subtypeEquiv fun φ ↦ by simp

variable {R}

@[simp]
theorem chartBaseChangeEquiv_apply_apply (x : Fin k → M)
    (N : chart A (fun i ↦ (1 : A) ⊗ₜ[R] x i)) (m : M) :
    (chartBaseChangeEquiv R A x N).1 m = (chartEquiv A _ N).1 (1 ⊗ₜ m) := by
  simp [chartBaseChangeEquiv]

@[simp]
theorem toSubmodule_chartBaseChangeEquiv_symm_apply (x : Fin k → M)
    (ψ : {ψ : M →ₗ[R] Fin k → A // ∀ i, ψ (x i) = Pi.single i 1}) :
    ((chartBaseChangeEquiv R A x).symm ψ).1.toSubmodule = LinearMap.ker (ψ.1.liftBaseChange A) :=
  (rfl)

/-- The chart points over `A` and `B` attached to `ψ : M → A^k` and to `f ∘ ψ : M → B^k` correspond
under base change along `f : A → B`. -/
theorem map_chartBaseChangeEquiv_symm (f : A →ₐ[R] B) (x : Fin k → M)
    (ψ : {ψ : M →ₗ[R] Fin k → A // ∀ i, ψ (x i) = Pi.single i 1}) :
    map f ((chartBaseChangeEquiv R A x).symm ψ).1 =
      ((chartBaseChangeEquiv R B x).symm ⟨f.toLinearMap.compLeft (Fin k) ∘ₗ ψ.1, fun i ↦ by
        ext j
        simp [ψ.2, Pi.single_apply, apply_ite f]⟩).1 :=
  map_ofSurjective_liftBaseChange f ψ.1
    (TauCeti.leftInverse_fintypeLinearCombination (x := fun i ↦ (1 : A) ⊗ₜ[R] x i)
      fun i ↦ by simp [ψ.2]).surjective

variable (R) in
/-- The chart at `x : Fin k → M` as a subfunctor of the Grassmannian functor
`A ↦ G(k, A ⊗[R] M; A)`: over `A`, it is the chart of `G(k, A ⊗[R] M; A)` at the family
`1 ⊗ₜ x i`. -/
def chartFunctor (x : Fin k → M) : Subfunctor (functor.{u, v, w} (R := R) (M := M) k) where
  obj A := chart A (fun i ↦ (1 : A) ⊗ₜ[R] x i)
  map {A B} f N hN := by
    obtain ⟨ψ, hψ⟩ := (chartBaseChangeEquiv R A x).symm.surjective ⟨N, hN⟩
    obtain rfl : ((chartBaseChangeEquiv R A x).symm ψ).1 = N := congrArg Subtype.val hψ
    -- the image of `N` under `(functor k).map f` is `map f.hom N`, a point of the chart over `B`
    have h : map f.hom ((chartBaseChangeEquiv R A x).symm ψ).1 ∈
        chart B (fun i ↦ (1 : B) ⊗ₜ[R] x i) := by
      rw [map_chartBaseChangeEquiv_symm]
      exact Subtype.prop _
    exact h

@[simp]
theorem mem_chartFunctor_obj_iff (x : Fin k → M) (A : CommAlgCat.{w} R)
    (N : G(k, A ⊗[R] M; A)) :
    N ∈ (chartFunctor R x).obj A ↔ N ∈ chart A (fun i ↦ (1 : A) ⊗ₜ[R] x i) :=
  (Iff.rfl)

end ChartFunctor

section ChartAlgebra

variable (R)

/-- The relations `ψ (x i) = eᵢ` defining the chart at `x`, as an ideal of the symmetric algebra on
`M^k`: an `R`-algebra map `g` out of the symmetric algebra is an `R`-linear map `M^k → A`, that is,
a family of `k` linear maps `ψⱼ : M → A`, and the relations say `ψⱼ (x i) = δᵢⱼ`. -/
def chartIdeal (x : Fin k → M) : Ideal (SymmetricAlgebra R (Fin k → M)) :=
  Ideal.span <| Set.range fun ij : Fin k × Fin k ↦
    SymmetricAlgebra.ι R (Fin k → M) (Pi.single ij.2 (x ij.1)) -
      algebraMap R _ ((Pi.single ij.1 1 : Fin k → R) ij.2)

/-- The coordinate ring of the chart at `x : Fin k → M`: the symmetric algebra on `M^k` modulo the
relations `ψ (x i) = eᵢ` (`Module.Grassmannian.chartIdeal`). Its `R`-algebra maps to `A` are the
points of the chart over `A` (`Module.Grassmannian.chartHomEquiv`). -/
abbrev ChartAlgebra (x : Fin k → M) : Type (max u v) :=
  SymmetricAlgebra R (Fin k → M) ⧸ chartIdeal R x

namespace ChartAlgebra

variable (x : Fin k → M)

/-- The universal point of the chart at `x`: the linear map `M → (ChartAlgebra R x)^k` whose `j`-th
component sends `m` to the class of the generator `Pi.single j m` of the symmetric algebra. -/
noncomputable def universalLinearMap : M →ₗ[R] Fin k → ChartAlgebra R x :=
  LinearMap.pi fun j ↦ (Ideal.Quotient.mkₐ R (chartIdeal R x)).toLinearMap ∘ₗ
    SymmetricAlgebra.ι R (Fin k → M) ∘ₗ LinearMap.single R (fun _ ↦ M) j

@[simp]
theorem universalLinearMap_apply_self (i : Fin k) :
    universalLinearMap R x (x i) = Pi.single i 1 := by
  ext j
  have h : SymmetricAlgebra.ι R (Fin k → M) (Pi.single j (x i)) -
      algebraMap R _ ((Pi.single i 1 : Fin k → R) j) ∈ chartIdeal R x :=
    Ideal.subset_span ⟨(i, j), rfl⟩
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem] at h
  simpa [universalLinearMap, Pi.single_apply, apply_ite (algebraMap R _)] using h

variable {A : Type w} [CommRing A] [Algebra R A]

/-- `R`-algebra maps `ChartAlgebra R x → A` are the linear maps `ψ : M → A^k` with `ψ (x i) = eᵢ`,
by composing with the universal point. -/
noncomputable def homEquiv :
    (ChartAlgebra R x →ₐ[R] A) ≃ {ψ : M →ₗ[R] Fin k → A // ∀ i, ψ (x i) = Pi.single i 1} where
  toFun g := ⟨g.toLinearMap.compLeft (Fin k) ∘ₗ universalLinearMap R x, fun i ↦ by
    ext j
    simp [universalLinearMap_apply_self, Pi.single_apply, apply_ite g]⟩
  invFun ψ := Ideal.Quotient.liftₐ (chartIdeal R x)
    (SymmetricAlgebra.lift (LinearMap.lsum R (fun _ ↦ M) R fun j ↦ LinearMap.proj j ∘ₗ ψ.1))
    (by
      -- the generators of `chartIdeal R x` are sent to `ψ (x i) j - δᵢⱼ = 0`
      have : chartIdeal R x ≤ RingHom.ker (SymmetricAlgebra.lift
          (LinearMap.lsum R (fun _ ↦ M) R fun j ↦ LinearMap.proj j ∘ₗ ψ.1) :
            SymmetricAlgebra R (Fin k → M) →ₐ[R] A) := by
        rw [chartIdeal, Ideal.span_le, Set.range_subset_iff]
        intro ij
        simp [-LinearMap.lsum_apply, LinearMap.lsum_piSingle, ψ.2, Pi.single_apply]
      exact fun a ha ↦ RingHom.mem_ker.1 (this ha))
  left_inv g := by
    refine Ideal.Quotient.algHom_ext R
      (SymmetricAlgebra.algHom_ext (LinearMap.pi_ext' fun j ↦ LinearMap.ext fun m ↦ ?_))
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [Ideal.Quotient.liftₐ_comp]
    simp [-LinearMap.lsum_apply, LinearMap.lsum_piSingle, universalLinearMap]
  right_inv ψ := by
    ext m j
    simp only [universalLinearMap, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.compLeft_apply, LinearMap.pi_apply, AlgHom.toLinearMap_apply]
    rw [← AlgHom.comp_apply _ (Ideal.Quotient.mkₐ R _), Ideal.Quotient.liftₐ_comp]
    simp [-LinearMap.lsum_apply, LinearMap.lsum_piSingle]

@[simp]
theorem homEquiv_apply_apply (g : ChartAlgebra R x →ₐ[R] A) (m : M) (j : Fin k) :
    (homEquiv R x g).1 m j = g (universalLinearMap R x m j) :=
  (rfl)

@[simp]
theorem homEquiv_symm_apply_universalLinearMap
    (ψ : {ψ : M →ₗ[R] Fin k → A // ∀ i, ψ (x i) = Pi.single i 1}) (m : M) (j : Fin k) :
    (homEquiv R x).symm ψ (universalLinearMap R x m j) = ψ.1 m j := by
  rw [← homEquiv_apply_apply, Equiv.apply_symm_apply]

/-- `R`-algebra maps out of `ChartAlgebra R x` are determined by their values on the universal
point. -/
theorem hom_ext {g g' : ChartAlgebra R x →ₐ[R] A}
    (h : ∀ m j, g (universalLinearMap R x m j) = g' (universalLinearMap R x m j)) : g = g' :=
  (homEquiv R x).injective <| Subtype.ext <| LinearMap.ext fun m ↦ funext fun j ↦ h m j

end ChartAlgebra

/-- The `R`-algebra maps `ChartAlgebra R x → A` are the points of the chart at `x` over `A`: the
point attached to `g` is the kernel of `A ⊗[R] M → A^k`, `a ⊗ₜ m ↦ a • g (ψ m)`, where `ψ` is the
universal point `ChartAlgebra.universalLinearMap R x`. -/
noncomputable def chartHomEquiv (x : Fin k → M) (A : Type w) [CommRing A] [Algebra R A] :
    (ChartAlgebra R x →ₐ[R] A) ≃ chart A (fun i ↦ (1 : A) ⊗ₜ[R] x i) :=
  (ChartAlgebra.homEquiv R x).trans (chartBaseChangeEquiv R A x).symm

variable {R}

@[simp]
theorem toSubmodule_chartHomEquiv_apply (x : Fin k → M) {A : Type w} [CommRing A] [Algebra R A]
    (g : ChartAlgebra R x →ₐ[R] A) :
    (chartHomEquiv R x A g).1.toSubmodule =
      LinearMap.ker ((g.toLinearMap.compLeft (Fin k) ∘ₗ
        ChartAlgebra.universalLinearMap R x).liftBaseChange A) :=
  (rfl)

@[simp]
theorem chartHomEquiv_symm_apply_universalLinearMap (x : Fin k → M) {A : Type w} [CommRing A]
    [Algebra R A] (N : chart A (fun i ↦ (1 : A) ⊗ₜ[R] x i)) (m : M) (j : Fin k) :
    (chartHomEquiv R x A).symm N (ChartAlgebra.universalLinearMap R x m j) =
      (chartEquiv A _ N).1 (1 ⊗ₜ m) j := by
  simp [chartHomEquiv]

/-- `chartHomEquiv` is natural: composing with `f : A → B` corresponds to base change of points
along `f`. -/
theorem chartHomEquiv_comp (x : Fin k → M) {A B : Type w} [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] (f : A →ₐ[R] B) (g : ChartAlgebra R x →ₐ[R] A) :
    (chartHomEquiv R x B (f.comp g)).1 = map f (chartHomEquiv R x A g).1 := by
  simp only [chartHomEquiv, Equiv.trans_apply, map_chartBaseChangeEquiv_symm]
  -- both points come from the linear map `m ↦ f ∘ g ∘ (universal point at m)`
  exact congrArg (fun ψ ↦ ((chartBaseChangeEquiv R B x).symm ψ).1) <|
    Subtype.ext <| LinearMap.ext fun m ↦ funext fun j ↦ by simp

/-- The chart subfunctor at `x` is corepresented by `ChartAlgebra R x`. -/
noncomputable def chartCorepresentableBy (x : Fin k → M) :
    (chartFunctor.{u, v, max u v} R x).toFunctor.CorepresentableBy
      (CommAlgCat.of R (ChartAlgebra R x)) where
  homEquiv {A} := ConcreteCategory.homEquiv.trans (chartHomEquiv R x A.carrier)
  -- `(chartFunctor R x).toFunctor.map f` acts on underlying points as `map f.hom`
  homEquiv_comp f g := Subtype.ext <| by exact chartHomEquiv_comp x f.hom g.hom

end ChartAlgebra

end Module.Grassmannian
