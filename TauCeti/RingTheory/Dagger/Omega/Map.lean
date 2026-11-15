/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Omega.Quotient
public import TauCeti.RingTheory.Kaehler.MapSemilinear
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import TauCeti.RingTheory.Dagger.NoetherNormalization
import TauCeti.RingTheory.Ideal.KrullIntersection
import TauCeti.RingTheory.Ideal.Quotient.Radical

/-!
# Functoriality of universally finite differentials

Let `f : A →ₐ[R] B` be a homomorphism of `R`-algebras. Unlike algebraic Kähler differentials, a
finite `B`-module need not remain finite when regarded as an `A`-module along `f`, so universal
finiteness alone does not make `Omega R A → Omega R B` tautological.

When `R` and `B` are noetherian and every maximal ideal `m` of `B` has `B ⧸ m` module-finite over
`R` — in particular for every `K`-dagger algebra `B` over a complete ultrametric normed field `K`
— functoriality holds without any finiteness or dagger hypothesis on the source `A`:

1. For every maximal ideal `m` of `B` and `n > 0`, `(m ^ n).radical = m`, so `B ⧸ m ^ n` is
   module-finite over `R` (`Ideal.moduleFinite_quotient_of_radical`).
2. For any finite `B`-module `M`, `M ⧸ (m ^ n • ⊤) ≃ (B ⧸ m ^ n) ⊗[B] M` is finite over
   `B ⧸ m ^ n`, hence finite (and noetherian) over `R`, so every `A`-submodule of
   `M ⧸ (m ^ n • ⊤)` is finitely generated over `A`.
3. Consequently `Omega.finiteKer R A` maps into `m ^ n • ⊤` for every maximal `m` and `n > 0`, and
   Krull intersection over all maximal ideals (`Ideal.iInf_isMaximal_pow_smul_eq_bot`) forces the
   induced map from `Ω[A⁄R]` to `M` to factor through `Omega R A`.

Applying this to `M = Omega K B` produces the `f`-semilinear pullback map
`Omega.mapSemilinear f : Omega K A →ₛₗ[f.toRingHom] Omega K B`, compatible with `ofKaehler`, `d`,
identity, composition, surjections, algebra equivalences, and the Jacobian expansion on
Monsky–Washnitzer algebras.

## Main definitions

* `TauCeti.Dagger.Omega.mapSemilinearOfFiniteResidue`: `f`-semilinear map
  `Omega R A →ₛₗ[f.toRingHom] Omega R B` when `B` is noetherian with `R`-finite residue fields and
  finite `Omega R B`.
* `TauCeti.Dagger.Omega.mapSemilinear`: `f`-semilinear pullback
  `Omega K A →ₛₗ[f.toRingHom] Omega K B` along `f : A →ₐ[K] B` into a `K`-dagger algebra `B`.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §4.1.
* E. Grosse-Klönne, *Finiteness of de Rham cohomology in rigid analysis*, Duke Math. J. 113
  (2002), §1.2.
* K. Kedlaya, *Finiteness of rigid cohomology with coefficients*, Duke Math. J. 134 (2006),
  §3.1.
-/

public section

namespace TauCeti.Dagger.Omega

open scoped Pointwise TensorProduct

/-- Universally finite differentials vanish when the structure map is surjective. -/
theorem subsingleton_of_surjective {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (h : Function.Surjective (algebraMap R A)) : Subsingleton (Omega R A) := by
  have := KaehlerDifferential.subsingleton_of_surjective R A h
  infer_instance

instance instSubsingletonSelf (R : Type*) [CommRing R] : Subsingleton (Omega R R) :=
  subsingleton_of_surjective Function.surjective_id

section FiniteResidue

variable {R A B : Type*} [CommRing R] [IsNoetherianRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [IsNoetherianRing B]

/-- If `B` is noetherian and every maximal ideal of `B` has `R`-finite quotient, then every
`f`-semilinear map `Ω[A⁄R] →ₛₗ[f.toRingHom] M` into a finite `B`-module vanishes on elements
killed by `Omega.ofKaehler R A`. -/
theorem map_eq_zero_of_ofKaehler_eq_zero {M : Type*} [AddCommGroup M]
    [Module R M] [Module B M] [IsScalarTower R B M] [Module.Finite B M]
    (hm : ∀ (m : Ideal B) [m.IsMaximal], Module.Finite R (B ⧸ m))
    (f : A →ₐ[R] B) (g : Ω[A⁄R] →ₛₗ[f.toRingHom] M) {x : Ω[A⁄R]}
    (hx : ofKaehler R A x = 0) : g x = 0 := by
  rw [← Submodule.mem_bot (R := B), ← Ideal.iInf_isMaximal_pow_smul_eq_bot (R := B) (M := M),
    Submodule.mem_iInf]
  intro m
  rw [Submodule.mem_iInf]
  intro hmMax
  rw [Submodule.mem_iInf]
  intro n
  rw [Submodule.mem_iInf]
  intro hn
  have hrad : (m ^ n).radical = m := (Ideal.radical_pow m hn.ne').trans hmMax.isPrime.radical
  have : (m ^ n).radical.IsMaximal := hrad.symm ▸ hmMax
  have : Module.Finite R (B ⧸ (m ^ n).radical) := hm (m ^ n).radical
  have : Module.Finite R (B ⧸ m ^ n) :=
    Ideal.moduleFinite_quotient_of_radical (m ^ n) (IsNoetherian.noetherian _)
  let P : Submodule B M := m ^ n • ⊤
  have : Module.Finite R ((B ⧸ m ^ n) ⊗[B] M) :=
    Module.Finite.trans (B ⧸ m ^ n) ((B ⧸ m ^ n) ⊗[B] M)
  have : Module.Finite R (M ⧸ P) :=
    Module.Finite.equiv ((TensorProduct.quotTensorEquivQuotSMul M (m ^ n)).restrictScalars R)
  let : Module A (M ⧸ P) := Module.compHom (M ⧸ P) f.toRingHom
  have : IsScalarTower R A (M ⧸ P) := IsScalarTower.of_algebraMap_smul fun r z ↦ by
    change f (algebraMap R A r) • z = r • z
    rw [f.commutes, algebraMap_smul]
  let q : Ω[A⁄R] →ₗ[A] M ⧸ P :=
    { toFun := fun z ↦ P.mkQ (g z)
      map_add' := fun z₁ z₂ ↦ by rw [map_add, map_add]
      map_smul' := fun a z ↦ by
        rw [g.map_smulₛₗ, LinearMap.map_smul]
        rfl }
  have : IsNoetherian A (M ⧸ P) := isNoetherian_of_tower R inferInstance
  have hquot : Module.Finite A (Ω[A⁄R] ⧸ LinearMap.ker q) :=
    Module.Finite.equiv q.quotKerEquivRange.symm
  have hxq : x ∈ LinearMap.ker q := (ofKaehler_eq_zero_iff.mp hx) (LinearMap.ker q) hquot
  exact (Submodule.Quotient.mk_eq_zero P).mp hxq

private noncomputable local instance (priority := low) {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R B] [Algebra A B] : Module A (Omega R B) :=
  Module.restrictScalars A B _

private local instance (priority := low) {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R B] [Algebra A B] : IsScalarTower A B (Omega R B) :=
  IsScalarTower.restrictScalars A B _

private noncomputable def mapAux [Algebra A B] [IsScalarTower R A B]
    [Module.Finite B (Omega R B)]
    (hm : ∀ (m : Ideal B) [m.IsMaximal], Module.Finite R (B ⧸ m)) :
    Omega R A →ₗ[A] Omega R B :=
  let gA : Ω[A⁄R] →ₗ[A] Omega R B :=
    (ofKaehler R B).restrictScalars A ∘ₗ KaehlerDifferential.map R R A B
  (ofKaehler R A).liftOfSurjective (ofKaehler_surjective R A)
    ⟨gA, fun _ hx ↦ map_eq_zero_of_ofKaehler_eq_zero hm (IsScalarTower.toAlgHom R A B)
      { toFun := gA
        map_add' := gA.map_add
        map_smul' := fun a z ↦ by
          rw [gA.map_smul]
          exact (IsScalarTower.algebraMap_smul B a (gA z)).symm } hx⟩

private theorem mapAux_ofKaehler [Algebra A B] [IsScalarTower R A B]
    [Module.Finite B (Omega R B)]
    (hm : ∀ (m : Ideal B) [m.IsMaximal], Module.Finite R (B ⧸ m)) (x : Ω[A⁄R]) :
    mapAux hm (ofKaehler R A x) = ofKaehler R B (KaehlerDifferential.map R R A B x) :=
  LinearMap.equivOfSurjective_apply (ofKaehler_surjective R A) _ (m := x)

/-- **Semilinear functoriality of `Omega` into a noetherian algebra with finite residue fields.** -/
noncomputable def mapSemilinearOfFiniteResidue [Module.Finite B (Omega R B)]
    (hm : ∀ (m : Ideal B) [m.IsMaximal], Module.Finite R (B ⧸ m))
    (f : A →ₐ[R] B) : Omega R A →ₛₗ[f.toRingHom] Omega R B :=
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  { toFun := mapAux hm
    map_add' := map_add _
    map_smul' := fun a ω ↦ by
      rw [LinearMap.map_smul]
      exact (IsScalarTower.algebraMap_smul B a (mapAux hm ω)).symm }

@[simp]
theorem mapSemilinearOfFiniteResidue_ofKaehler [Module.Finite B (Omega R B)]
    (hm : ∀ (m : Ideal B) [m.IsMaximal], Module.Finite R (B ⧸ m))
    (f : A →ₐ[R] B) (x : Ω[A⁄R]) :
    mapSemilinearOfFiniteResidue hm f (ofKaehler R A x) =
      ofKaehler R B (KaehlerDifferential.mapSemilinear f x) :=
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  (mapAux_ofKaehler hm x).trans
    (congrArg (ofKaehler R B) (KaehlerDifferential.mapSemilinear_toAlgHom_apply x).symm)

@[simp]
theorem mapSemilinearOfFiniteResidue_d [Module.Finite B (Omega R B)]
    (hm : ∀ (m : Ideal B) [m.IsMaximal], Module.Finite R (B ⧸ m))
    (f : A →ₐ[R] B) (a : A) :
    mapSemilinearOfFiniteResidue hm f (d R A a) = d R B (f a) := by
  rw [← ofKaehler_D, mapSemilinearOfFiniteResidue_ofKaehler, KaehlerDifferential.mapSemilinear_D,
    ofKaehler_D]

end FiniteResidue

section Dagger

variable {K A B C : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CommRing A] [CommRing B] [CommRing C] [Algebra K A] [Algebra K B] [Algebra K C]

/-- **Functoriality of universally finite differentials into a dagger algebra.** An algebra
homomorphism `f : A →ₐ[K] B` from an arbitrary `K`-algebra `A` into a `K`-dagger algebra `B`
induces the `f`-semilinear map `Omega K A →ₛₗ[f.toRingHom] Omega K B` sending `d a` to `d (f a)`. -/
noncomputable def mapSemilinear [IsDaggerAlgebra K B] (f : A →ₐ[K] B) :
    Omega K A →ₛₗ[f.toRingHom] Omega K B :=
  have := IsDaggerAlgebra.isNoetherianRing (K := K) (A := B)
  mapSemilinearOfFiniteResidue (IsDaggerAlgebra.finite_quotient_of_isMaximal K) f

@[simp]
theorem mapSemilinear_ofKaehler [IsDaggerAlgebra K B] (f : A →ₐ[K] B) (x : Ω[A⁄K]) :
    mapSemilinear f (ofKaehler K A x) = ofKaehler K B (KaehlerDifferential.mapSemilinear f x) := by
  have := IsDaggerAlgebra.isNoetherianRing (K := K) (A := B)
  exact mapSemilinearOfFiniteResidue_ofKaehler (IsDaggerAlgebra.finite_quotient_of_isMaximal K) f x

@[simp]
theorem mapSemilinear_d [IsDaggerAlgebra K B] (f : A →ₐ[K] B) (a : A) :
    mapSemilinear f (d K A a) = d K B (f a) := by
  have := IsDaggerAlgebra.isNoetherianRing (K := K) (A := B)
  exact mapSemilinearOfFiniteResidue_d (IsDaggerAlgebra.finite_quotient_of_isMaximal K) f a

@[simp]
theorem mapSemilinear_smul [IsDaggerAlgebra K B] (f : A →ₐ[K] B) (a : A) (ω : Omega K A) :
    mapSemilinear f (a • ω) = f a • mapSemilinear f ω :=
  (mapSemilinear f).map_smulₛₗ a ω

theorem mapSemilinear_id [IsDaggerAlgebra K A] :
    (mapSemilinear (AlgHom.id K A) : Omega K A →ₗ[A] Omega K A) = LinearMap.id :=
  hom_ext fun a ↦ mapSemilinear_d (AlgHom.id K A) a

@[simp]
theorem mapSemilinear_id_apply [IsDaggerAlgebra K A] (ω : Omega K A) :
    mapSemilinear (AlgHom.id K A) ω = ω :=
  DFunLike.congr_fun mapSemilinear_id ω

@[simp]
theorem mapSemilinear_comp_apply [IsDaggerAlgebra K B] [IsDaggerAlgebra K C]
    (g : B →ₐ[K] C) (f : A →ₐ[K] B) (ω : Omega K A) :
    mapSemilinear (g.comp f) ω = mapSemilinear g (mapSemilinear f ω) := by
  obtain ⟨x, rfl⟩ := ofKaehler_surjective K A ω
  rw [mapSemilinear_ofKaehler, mapSemilinear_ofKaehler, mapSemilinear_ofKaehler,
    KaehlerDifferential.mapSemilinear_comp_apply]

theorem mapSemilinear_comp [IsDaggerAlgebra K B] [IsDaggerAlgebra K C]
    (g : B →ₐ[K] C) (f : A →ₐ[K] B) :
    mapSemilinear (g.comp f) = (mapSemilinear g).comp (mapSemilinear f) :=
  LinearMap.ext (mapSemilinear_comp_apply g f)

@[simp]
theorem mapSemilinear_apply_symm_apply [IsDaggerAlgebra K A] [IsDaggerAlgebra K B]
    (e : A ≃ₐ[K] B) (ω : Omega K B) :
    mapSemilinear e.toAlgHom (mapSemilinear e.symm.toAlgHom ω) = ω := by
  rw [← mapSemilinear_comp_apply, AlgEquiv.comp_symm, mapSemilinear_id_apply]

@[simp]
theorem mapSemilinear_symm_apply_apply [IsDaggerAlgebra K A] [IsDaggerAlgebra K B]
    (e : A ≃ₐ[K] B) (ω : Omega K A) :
    mapSemilinear e.symm.toAlgHom (mapSemilinear e.toAlgHom ω) = ω :=
  mapSemilinear_apply_symm_apply e.symm ω

/-- A surjective homomorphism onto a dagger algebra induces a surjective map on `Omega`. -/
theorem mapSemilinear_surjective [IsDaggerAlgebra K B] {f : A →ₐ[K] B}
    (hf : Function.Surjective f) : Function.Surjective (mapSemilinear f) := by
  intro y
  have hy : y ∈ Submodule.span B (Set.range (d K B)) := span_range_d K B ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem _ hd =>
    obtain ⟨b, rfl⟩ := hd
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨d K A a, mapSemilinear_d f a⟩
  | zero => exact ⟨0, map_zero _⟩
  | add _ _ _ _ ih₁ ih₂ =>
    obtain ⟨x₁, rfl⟩ := ih₁
    obtain ⟨x₂, rfl⟩ := ih₂
    exact ⟨x₁ + x₂, map_add _ x₁ x₂⟩
  | smul b _ _ ih =>
    obtain ⟨a, rfl⟩ := hf b
    obtain ⟨x, rfl⟩ := ih
    exact ⟨a • x, mapSemilinear_smul f a x⟩

/-- Any algebra homomorphism `A →ₐ[K] K` to the coefficient field induces the zero map on
`Omega`, since `Omega K K` is subsingleton. -/
@[simp]
theorem mapSemilinear_toSelf (φ : A →ₐ[K] K) (ω : Omega K A) :
    mapSemilinear φ ω = 0 :=
  Subsingleton.elim _ _

/-- **Jacobian formula for `mapSemilinear` on Monsky–Washnitzer algebras**: pulling back `dXᵢ`
along `f : K⟨X⟩† →ₐ[K] K⟨Y⟩†` expands in the target coordinate differentials with the partial
derivatives of `f Xᵢ`. -/
theorem mapSemilinear_d_X {σ τ : Type*} [Fintype τ]
    (f : washnitzerAlgebra σ K →ₐ[K] washnitzerAlgebra τ K) (i : σ) :
    mapSemilinear f (d K _ (washnitzerAlgebra.X σ K i)) =
      ∑ j, washnitzerAlgebra.pderiv τ K j (f (washnitzerAlgebra.X σ K i)) •
        d K _ (washnitzerAlgebra.X τ K j) :=
  (mapSemilinear_d f (washnitzerAlgebra.X σ K i)).trans
    (d_eq_sum (f (washnitzerAlgebra.X σ K i)))

end Dagger

end TauCeti.Dagger.Omega
