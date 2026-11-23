/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.Comultiplication
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Contraction
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.FiniteStability
import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Descent
import TauCeti.Algebra.Coalgebra.GroupLike.ScalarAut
import TauCeti.Algebra.TensorProduct.CommonOverfield
import TauCeti.AlgebraicGeometry.AugmentationPoint.ConnectedComponent

/-!
# The geometric identity component under automorphisms and connected groups

For an affine group `G` of finite type over a ring `k` and an algebraically closed extension
`L / k`, the identity component of `G_L` is cut out by the Hopf ideal
`TauCeti.HopfAlgebra.identityComponentHopfIdeal`. This file proves two facts about it that are
the inputs of its Galois descent to `k`:

* the action of `Aut(L / k)` on the scalar factor of `L ⊗[k] O(G)` preserves this ideal;
* a homomorphism `M → G_K` from a geometrically connected affine group over another extension
  `K / k` kills every function on `G` whose extension to `L` lies in this ideal.

Over a perfect field `k`, Galois descent along `AlgebraicClosure k / k` then defines the identity
component over `k`. As an application, the smallest closed `k`-subgroup of `G` through whose base
change to `K` a family of homomorphisms from geometrically connected groups factors is
geometrically connected, provided this subgroup is of finite type.

## Main declarations

* `TauCeti.CommHopfAlgCat.map_mem_identityComponentHopfIdeal_baseChange_iff`: the identity
  component of a base-changed affine group is stable under `Aut(L / k)` acting on the scalar
  factor.
* `TauCeti.CommHopfAlgCat.apply_one_tmul_eq_zero_of_mem_identityComponentHopfIdeal`: a
  homomorphism from a geometrically connected group kills the functions over `k` whose scalar
  extensions belong to the ideal cutting out the geometric identity component.
* `TauCeti.CommHopfAlgCat.geometricallyConnected_quotient_contractHopfIdeal_commonKernelHopfIdeal`:
  the smallest closed subgroup over a perfect field through whose base change a family of
  homomorphisms from geometrically connected groups factors is geometrically connected, when it is
  of finite type.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37 (the identity component) and
  Appendix A (Galois descent).
-/

public section

open CategoryTheory _root_.CommHopfAlgCat
open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u u' v w

section GaloisStable

variable {k : Type u} {L : Type w} [CommRing k] [Field L] [IsAlgClosed L] [Algebra k L]
variable {A : _root_.CommHopfAlgCat.{v} k} [Algebra.FiniteType k A]

/-- **The geometric identity component is Galois stable.** Let `A` be the coordinate Hopf algebra
of an affine group of finite type over `k`, and `L / k` an algebraically closed extension. An
automorphism `σ` of `L / k`, acting on the scalar factor of `L ⊗[k] A`, preserves the Hopf ideal
cutting out the identity component of the base change, and so does its inverse. -/
theorem map_mem_identityComponentHopfIdeal_baseChange_iff (σ : L ≃ₐ[k] L) {x : L ⊗[k] A} :
    TensorProduct.map σ.toLinearMap LinearMap.id x ∈
        HopfAlgebra.identityComponentHopfIdeal (k := L) (H := baseChange (K := L) A) ↔
      x ∈ HopfAlgebra.identityComponentHopfIdeal (k := L) (H := baseChange (K := L) A) := by
  let _ : IsNoetherianRing (baseChange (K := L) A) := Algebra.FiniteType.isNoetherianRing L _
  let τ : (L ⊗[k] A) ≃+* (L ⊗[k] A) := (ScalarAut.toAlgAut (A := (A : Type v)) σ).toRingEquiv
  have hτ : τ x = TensorProduct.map σ.toLinearMap LinearMap.id x := by
    induction x using TensorProduct.inductionOn with
    | tmul l a => simp [τ]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hε (y : baseChange (K := L) A) :
      Bialgebra.counitAlgHom L (baseChange (K := L) A) (τ y) =
        σ (Bialgebra.counitAlgHom L (baseChange (K := L) A) y) :=
    ScalarAut.counit_smul σ y
  have hz : PrimeSpectrum.comap (τ : (L ⊗[k] A) →+* (L ⊗[k] A))
      (Bialgebra.augmentationPoint L (baseChange (K := L) A)) =
        Bialgebra.augmentationPoint L (baseChange (K := L) A) := by
    ext y
    -- `augmentationPoint` is a point of `Spec`, whose underlying type is `PrimeSpectrum`, so the
    -- lemmas about `PrimeSpectrum.comap` do not match it syntactically; unfold membership.
    change τ y ∈ (Bialgebra.augmentationPoint L (baseChange (K := L) A)).asIdeal ↔ _
    rw [AlgHom.kernelPoint_asIdeal, RingHom.mem_ker, RingHom.mem_ker]
    exact (Eq.congr_left (hε y)).trans (map_eq_zero_iff σ σ.injective)
  rw [HopfAlgebra.mem_identityComponentHopfIdeal, HopfAlgebra.mem_identityComponentHopfIdeal, ← hτ]
  exact PrimeSpectrum.apply_mem_connectedComponentIdeal_iff_of_comap_eq_self τ _ hz

end GaloisStable

/-- **A connected group maps into the identity component.** Let `A` be the coordinate Hopf algebra
of an affine group `G` of finite type over a field `k`, `L / k` an algebraically closed extension
and `K / k` any extension. Let `g : M → G_K` be a homomorphism from a geometrically connected
affine group `M` over `K` with coordinate Hopf algebra `T`. A function `x` on `G` whose base change
to `L` lies in the ideal of the identity component of `G_L` is killed by `g`. -/
theorem apply_one_tmul_eq_zero_of_mem_identityComponentHopfIdeal
    {k : Type u} {K : Type u'} {L : Type w} [Field k] [Field K] [Algebra k K] [Field L]
    [IsAlgClosed L] [Algebra k L] {A : _root_.CommHopfAlgCat.{v} k} [Algebra.FiniteType k A]
    {T : _root_.CommHopfAlgCat.{max u' v} K} (hT : geometricallyConnectedCommHopfAlgProperty K T)
    (g : baseChange (K := K) A ⟶ T) {x : A}
    (hx : (1 : L) ⊗ₜ[k] x ∈
      HopfAlgebra.identityComponentHopfIdeal (k := L) (H := baseChange (K := L) A)) :
    g.hom ((1 : K) ⊗ₜ[k] x) = 0 := by
  let _ : IsNoetherianRing (baseChange (K := L) A) := Algebra.FiniteType.isNoetherianRing L _
  let d := Algebra.TensorProduct.commonOverfield k K L
  let φ : L ⊗[k] A →+* d.Ω ⊗[K] T :=
    (Algebra.TensorProduct.map (AlgHom.id d.Ω d.Ω) g.hom.toAlgHom).toRingHom.comp
      ((Algebra.TensorProduct.cancelBaseChange k K d.Ω d.Ω A).symm.toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.map d.right (AlgHom.id k A)).toRingHom)
  let ψ := Bialgebra.counitAlgHom d.Ω (d.Ω ⊗[K] T)
  have hψφ (y : baseChange (K := L) A) :
      ψ (φ y) = d.right (Bialgebra.counitAlgHom L (baseChange (K := L) A) y) := by
    induction y using TensorProduct.inductionOn with
    | tmul l a =>
      simp [φ, ψ, Bialgebra.counitAlgHom_apply, Algebra.smul_def, mul_comm,
        ← IsScalarTower.algebraMap_apply]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hconn : ConnectedSpace (PrimeSpectrum (d.Ω ⊗[K] T)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.comm K T d.Ω).toRingEquiv).connectedSpace_iff.mp
      (hT.connectedSpace_tensorProduct K d.Ω T)
  set e := PrimeSpectrum.connectedComponentIdempotent
    (Bialgebra.augmentationPoint L (baseChange (K := L) A))
  have he : φ e = 1 := by
    have hidem : IsIdempotentElem (φ e) :=
      (PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent _).map φ
    rcases hidem.eq_zero_or_eq_one_of_preconnectedSpace with h0 | h1
    · have h := hψφ e
      rw [h0, map_zero, AlgHom.map_connectedComponentIdempotent_kernelPoint_eq_one,
        map_one] at h
      exact absurd h zero_ne_one
    · exact h1
  rw [HopfAlgebra.mem_identityComponentHopfIdeal] at hx
  obtain ⟨a, ha⟩ := PrimeSpectrum.mem_connectedComponentIdeal_iff.mp hx
  have h₁ : φ (1 ⊗ₜ x) = (1 : d.Ω) ⊗ₜ[K] g.hom (1 ⊗ₜ x) := by
    simp [φ]
  have h₂ : φ (1 ⊗ₜ x) = 0 := by
    rw [← ha, map_mul, map_sub, map_one, he, sub_self, mul_zero]
  exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff K T _).mp (h₁.symm.trans h₂)

/-- **Groups generated by connected groups are connected.** Let `k` be a perfect field, `K / k`
a field extension, `G` an affine group over `k` with coordinate Hopf algebra `H`, and
`f i : M_i → G_K` a family of homomorphisms from geometrically connected affine groups over `K`.
The smallest closed `k`-subgroup of `G` through whose base change to `K` every `f i` factors, cut
out by `contractHopfIdeal (commonKernelHopfIdeal f)`, is geometrically connected when it is of
finite type. -/
theorem geometricallyConnected_quotient_contractHopfIdeal_commonKernelHopfIdeal
    {k : Type u} {K : Type u'} [Field k] [PerfectField k] [Field K] [Algebra k K]
    {H : _root_.CommHopfAlgCat.{v} k} {ι : Type*} {T : ι → _root_.CommHopfAlgCat.{max u' v} K}
    (f : ∀ i, baseChange (K := K) H ⟶ T i)
    (hT : ∀ i, geometricallyConnectedCommHopfAlgProperty K (T i))
    [Algebra.FiniteType k (quotient H (contractHopfIdeal (commonKernelHopfIdeal f)))] :
    geometricallyConnectedCommHopfAlgProperty k
      (quotient H (contractHopfIdeal (commonKernelHopfIdeal f))) := by
  set J := contractHopfIdeal (commonKernelHopfIdeal f)
  let L := AlgebraicClosure k
  have : IsGalois k L := {}
  let E : HopfIdeal L (baseChange (K := L) (quotient H J)) :=
    HopfAlgebra.identityComponentHopfIdeal
  obtain ⟨I, hI, -⟩ := (existsUnique_baseChangeHopfIdeal_eq_iff E).mpr
    fun σ _ hx ↦ (map_mem_identityComponentHopfIdeal_baseChange_iff σ).mpr hx
  have hf (i : ι) :
      (baseChangeHopfIdeal (K := K) J).toIdeal ≤ RingHom.ker (f i).hom.toAlgHom.toRingHom :=
    (le_contractHopfIdeal_commonKernelHopfIdeal_iff f J).mp le_rfl i
  have hI'J : I.comapOfSurjective (mkQuotient H J).hom (mkQuotient_surjective H J) ≤ J := by
    refine (le_contractHopfIdeal_commonKernelHopfIdeal_iff f _).mpr fun i ↦ ?_
    rw [baseChangeHopfIdeal_toIdeal, Ideal.map_le_iff_le_comap]
    intro y hy
    have hmem : (1 : L) ⊗ₜ[k] (mkQuotient H J).hom y ∈ E :=
      hI ▸ one_tmul_mem_baseChangeHopfIdeal (HopfIdeal.mem_comapOfSurjective.mp hy)
    have hcomp := congrArg (fun g ↦ g.hom ((1 : K) ⊗ₜ[k] y))
      (baseChangeMap_mkQuotient_comp_baseChangeLiftQuotient J (f i) (hf i))
    simp only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply] at hcomp
    rw [Ideal.mem_comap, RingHom.mem_ker]
    simpa [← hcomp] using apply_one_tmul_eq_zero_of_mem_identityComponentHopfIdeal (hT i)
      (baseChangeLiftQuotient J (f i) (hf i)) hmem
  have hE : E = ⊥ := by rw [← hI, eq_bot_of_comapOfSurjective_le I hI'J, baseChangeHopfIdeal_bot]
  rw [geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_baseChange k L]
  exact HopfAlgebra.identityComponentHopfIdeal_eq_bot_iff_connectedSpace.mp hE

end TauCeti.CommHopfAlgCat
