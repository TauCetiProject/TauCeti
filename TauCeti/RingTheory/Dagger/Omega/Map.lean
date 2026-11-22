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

For `f : A →ₐ[R] B` where `R` and `B` are noetherian and every maximal ideal `m` of `B` has
`B ⧸ m` module-finite over `R` (in particular any `K`-dagger algebra `B`), any `f`-semilinear map
`Ω[A⁄R] →ₛₗ[f] M` into a finite `B`-module factors through `Omega R A`: for each maximal `m` and
`n > 0`, `M ⧸ (m ^ n • ⊤)` is `R`-finite (hence `A`-noetherian), so Krull intersection over maximal
ideals forces every such `g` to kill `Omega.finiteKer R A` and therefore descend to `Omega R A`.

## References

* E. Grosse-Klönne, *Finiteness of de Rham cohomology in rigid analysis*, Duke Math. J. 113
  (2002), §1.2.
* K. Kedlaya, *Finiteness of rigid cohomology with coefficients*, Duke Math. J. 134 (2006), §3.1.
-/

public section

namespace TauCeti.Dagger.Omega

open scoped Pointwise TensorProduct

section FiniteResidue
variable {R A B : Type*} [CommRing R] [IsNoetherianRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [IsNoetherianRing B]

/-- If `B` is noetherian with maximal residue fields `B ⧸ m` module-finite over `R`, then every
`f`-semilinear map `Ω[A⁄R] →ₛₗ[f.toRingHom] M` into a finite `B`-module vanishes on elements
killed by `Omega.ofKaehler R A`. -/
theorem map_eq_zero_of_ofKaehler_eq_zero {M : Type*} [AddCommGroup M]
    [Module R M] [Module B M] [IsScalarTower R B M] [Module.Finite B M]
    (hm : ∀ (m : Ideal B) [m.IsMaximal], Module.Finite R (B ⧸ m))
    (f : A →ₐ[R] B) (g : Ω[A⁄R] →ₛₗ[f.toRingHom] M) {x : Ω[A⁄R]}
    (hx : ofKaehler R A x = 0) : g x = 0 := by
  simp only [← Submodule.mem_bot (R := B),
    ← Ideal.iInf_isMaximal_pow_smul_eq_bot (R := B) (M := M), Submodule.mem_iInf]
  intro m hmMax n hn
  have hrad : (m ^ n).radical = m := (Ideal.radical_pow m hn.ne').trans hmMax.isPrime.radical
  have : (m ^ n).radical.IsMaximal := hrad.symm ▸ hmMax
  have : Module.Finite R (B ⧸ (m ^ n).radical) := hm (m ^ n).radical
  have : Module.Finite R (B ⧸ m ^ n) :=
    Ideal.moduleFinite_quotient_of_radical (m ^ n) (IsNoetherian.noetherian _)
  let P : Submodule B M := m ^ n • ⊤
  have : Module.Finite R ((B ⧸ m ^ n) ⊗[B] M) := Module.Finite.trans (B ⧸ m ^ n) _
  have : Module.Finite R (M ⧸ P) :=
    Module.Finite.equiv ((TensorProduct.quotTensorEquivQuotSMul M (m ^ n)).restrictScalars R)
  let : Module A (M ⧸ P) := Module.compHom (M ⧸ P) f.toRingHom
  have : IsScalarTower R A (M ⧸ P) := IsScalarTower.of_algebraMap_smul fun r z ↦ by
    rw [MulAction.compHom_smul_def (f.toRingHom : A →* B), MonoidHom.coe_ofClass,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, f.commutes, algebraMap_smul]
  let q : Ω[A⁄R] →ₗ[A] M ⧸ P :=
    { toFun := fun z ↦ P.mkQ (g z)
      map_add' := fun _ _ ↦ by rw [map_add, map_add]
      map_smul' := fun a z ↦ by rw [g.map_smulₛₗ, LinearMap.map_smul]; rfl }
  have : IsNoetherian A (M ⧸ P) := isNoetherian_of_tower R inferInstance
  exact (Submodule.Quotient.mk_eq_zero P).mp <|
    (ofKaehler_eq_zero_iff.mp hx) (LinearMap.ker q) (Module.Finite.equiv q.quotKerEquivRange.symm)

/-- **Semilinear functoriality of `Omega`** along `f : A →ₐ[R] B` when `R` and `B` are noetherian,
every maximal residue field `B ⧸ m` is module-finite over `R`, and `Omega R B` is finite over `B`.
The induced `f`-semilinear map `Omega R A →ₛₗ[f.toRingHom] Omega R B` sends `d R A a` to
`d R B (f a)`. -/
noncomputable def mapSemilinearOfFiniteResidue [Module.Finite B (Omega R B)]
    (hm : ∀ (m : Ideal B) [m.IsMaximal], Module.Finite R (B ⧸ m))
    (f : A →ₐ[R] B) : Omega R A →ₛₗ[f.toRingHom] Omega R B :=
  letI : Module A (Omega R B) := Module.compHom (Omega R B) f.toRingHom
  let g : Ω[A⁄R] →ₛₗ[f.toRingHom] Omega R B :=
    (ofKaehler R B).comp (KaehlerDifferential.mapSemilinear f)
  let hA : Omega R A →ₗ[A] Omega R B := (ofKaehler R A).liftOfSurjective (ofKaehler_surjective R A)
    ⟨{ toFun := g, map_add' := g.map_add, map_smul' := fun a z ↦ g.map_smulₛₗ a z },
      fun _ hx ↦ map_eq_zero_of_ofKaehler_eq_zero hm f g hx⟩
  { toFun := hA, map_add' := hA.map_add, map_smul' := fun a ω ↦ hA.map_smul a ω }

@[simp] theorem mapSemilinearOfFiniteResidue_ofKaehler [Module.Finite B (Omega R B)]
    (hm : ∀ (m : Ideal B) [m.IsMaximal], Module.Finite R (B ⧸ m))
    (f : A →ₐ[R] B) (x : Ω[A⁄R]) :
    mapSemilinearOfFiniteResidue hm f (ofKaehler R A x) =
      ofKaehler R B (KaehlerDifferential.mapSemilinear f x) := by
  let : Module A (Omega R B) := Module.compHom (Omega R B) f.toRingHom
  dsimp only [mapSemilinearOfFiniteResidue, LinearMap.coe_mk, AddHom.coe_mk]
  exact LinearMap.equivOfSurjective_apply (ofKaehler_surjective R A) _ (m := x)
@[simp] theorem mapSemilinearOfFiniteResidue_d [Module.Finite B (Omega R B)]
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
homomorphism `f : A →ₐ[K] B` into a `K`-dagger algebra `B` induces `Omega K A →ₛₗ[f] Omega K B`
sending `d a` to `d (f a)`. -/
noncomputable def mapSemilinear [IsDaggerAlgebra K B] (f : A →ₐ[K] B) :
    Omega K A →ₛₗ[f.toRingHom] Omega K B :=
  have := IsDaggerAlgebra.isNoetherianRing (K := K) (A := B)
  mapSemilinearOfFiniteResidue (IsDaggerAlgebra.finite_quotient_of_isMaximal K) f

@[simp] theorem mapSemilinear_ofKaehler [IsDaggerAlgebra K B] (f : A →ₐ[K] B) (x : Ω[A⁄K]) :
    mapSemilinear f (ofKaehler K A x) = ofKaehler K B (KaehlerDifferential.mapSemilinear f x) :=
  have := IsDaggerAlgebra.isNoetherianRing (K := K) (A := B)
  mapSemilinearOfFiniteResidue_ofKaehler (IsDaggerAlgebra.finite_quotient_of_isMaximal K) f x
@[simp] theorem mapSemilinear_d [IsDaggerAlgebra K B] (f : A →ₐ[K] B) (a : A) :
    mapSemilinear f (d K A a) = d K B (f a) := by
  rw [← ofKaehler_D, mapSemilinear_ofKaehler, KaehlerDifferential.mapSemilinear_D, ofKaehler_D]
@[simp] theorem mapSemilinear_smul [IsDaggerAlgebra K B] (f : A →ₐ[K] B) (a : A) (ω : Omega K A) :
    mapSemilinear f (a • ω) = f a • mapSemilinear f ω := (mapSemilinear f).map_smulₛₗ a ω
theorem mapSemilinear_id [IsDaggerAlgebra K A] :
    (mapSemilinear (AlgHom.id K A) : Omega K A →ₗ[A] Omega K A) = LinearMap.id :=
  hom_ext fun a ↦ mapSemilinear_d (AlgHom.id K A) a
@[simp] theorem mapSemilinear_id_apply [IsDaggerAlgebra K A] (ω : Omega K A) :
    mapSemilinear (AlgHom.id K A) ω = ω := DFunLike.congr_fun mapSemilinear_id ω
@[simp] theorem mapSemilinear_comp_apply [IsDaggerAlgebra K B] [IsDaggerAlgebra K C]
    (g : B →ₐ[K] C) (f : A →ₐ[K] B) (ω : Omega K A) :
    mapSemilinear (g.comp f) ω = mapSemilinear g (mapSemilinear f ω) := by
  obtain ⟨x, rfl⟩ := ofKaehler_surjective K A ω
  simp only [mapSemilinear_ofKaehler, KaehlerDifferential.mapSemilinear_comp_apply]
theorem mapSemilinear_comp [IsDaggerAlgebra K B] [IsDaggerAlgebra K C]
    (g : B →ₐ[K] C) (f : A →ₐ[K] B) :
    mapSemilinear (g.comp f) = (mapSemilinear g).comp (mapSemilinear f) :=
  LinearMap.ext (mapSemilinear_comp_apply g f)
@[simp] theorem mapSemilinear_apply_symm_apply [IsDaggerAlgebra K A] [IsDaggerAlgebra K B]
    (e : A ≃ₐ[K] B) (ω : Omega K B) :
    mapSemilinear e.toAlgHom (mapSemilinear e.symm.toAlgHom ω) = ω := by
  rw [← mapSemilinear_comp_apply, AlgEquiv.comp_symm, mapSemilinear_id_apply]
@[simp] theorem mapSemilinear_symm_apply_apply [IsDaggerAlgebra K A] [IsDaggerAlgebra K B]
    (e : A ≃ₐ[K] B) (ω : Omega K A) :
    mapSemilinear e.symm.toAlgHom (mapSemilinear e.toAlgHom ω) = ω :=
  mapSemilinear_apply_symm_apply e.symm ω

/-- A surjective homomorphism onto a dagger algebra induces a surjective map on `Omega`. -/
theorem mapSemilinear_surjective [IsDaggerAlgebra K B] {f : A →ₐ[K] B}
    (hf : Function.Surjective f) : Function.Surjective (mapSemilinear f) := by
  have : RingHomSurjective f.toRingHom := ⟨hf⟩
  have h : Submodule.span B (Set.range (d K B)) ≤ LinearMap.range (mapSemilinear f) := by
    rw [Submodule.span_le]; rintro _ ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := hf b; exact ⟨d K A a, mapSemilinear_d f a⟩
  exact fun y ↦ h (span_range_d K B ▸ Submodule.mem_top)

/-- Any algebra homomorphism `A →ₐ[K] K` induces the zero map on `Omega`. -/
@[simp] theorem mapSemilinear_toSelf (φ : A →ₐ[K] K) (ω : Omega K A) :
    mapSemilinear φ ω = 0 := Subsingleton.elim _ _

/-- **Jacobian formula for `mapSemilinear` on Monsky–Washnitzer algebras.** -/
theorem mapSemilinear_d_X {σ τ : Type*} [Fintype τ]
    (f : washnitzerAlgebra σ K →ₐ[K] washnitzerAlgebra τ K) (i : σ) :
    mapSemilinear f (d K _ (washnitzerAlgebra.X σ K i)) =
      ∑ j, washnitzerAlgebra.pderiv τ K j (f (washnitzerAlgebra.X σ K i)) •
        d K _ (washnitzerAlgebra.X τ K j) :=
  (mapSemilinear_d f (washnitzerAlgebra.X σ K i)).trans (d_eq_sum (f (washnitzerAlgebra.X σ K i)))
end Dagger

end TauCeti.Dagger.Omega
