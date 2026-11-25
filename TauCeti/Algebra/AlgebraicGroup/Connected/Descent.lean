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
* `TauCeti.CommHopfAlgCat.existsUnique_baseChangeHopfIdeal_eq_identityComponentHopfIdeal`: over a
  perfect field, the identity component of the geometric fibre descends to a unique Hopf ideal.
* `geometricallyConnectedCommHopfAlgProperty_quotient_contractHopfIdeal_commonKernelHopfIdeal`:
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
  -- `ScalarAut.toAlgAut σ` is defined as the congruence that `ScalarAut.smul_def` names.
  have hτ (y : L ⊗[k] A) : τ y = σ • y := (ScalarAut.smul_def σ y).symm
  have hτmap : τ x = TensorProduct.map σ.toLinearMap LinearMap.id x :=
    ScalarAut.toAlgAut_apply σ x
  have hz : PrimeSpectrum.comap (τ : (L ⊗[k] A) →+* (L ⊗[k] A))
      (Bialgebra.augmentationPoint L (baseChange (K := L) A)) =
        Bialgebra.augmentationPoint L (baseChange (K := L) A) :=
    AlgHom.comap_kernelPoint_of_apply_eq _ _ _ (σ : L →+* L) σ.injective fun y ↦ by
      simpa only [Bialgebra.counitAlgHom_apply, RingHom.coe_coe, hτ] using ScalarAut.counit_smul σ y
  rw [HopfAlgebra.mem_identityComponentHopfIdeal, HopfAlgebra.mem_identityComponentHopfIdeal,
    ← hτmap]
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
  let _ : Algebra L d.Ω := d.right.toRingHom.toAlgebra
  have : IsScalarTower k L d.Ω := IsScalarTower.of_algHom d.right
  -- The base change to `d.Ω` of `g`, read through the tower comparisons `L → d.Ω` and `K → d.Ω`.
  let e : d.Ω ⊗[L] (L ⊗[k] A) →ₐc[d.Ω] d.Ω ⊗[K] T :=
    (Bialgebra.TensorProduct.map (BialgHom.id d.Ω d.Ω) g.hom).comp
      ((Bialgebra.TensorProduct.baseChangeTowerBialgEquiv k L A d.Ω).trans
        (Bialgebra.TensorProduct.baseChangeTowerBialgEquiv k K A d.Ω).symm).toBialgHom
  let φ : L ⊗[k] A →+* d.Ω ⊗[K] T :=
    (e : d.Ω ⊗[L] (L ⊗[k] A) →ₐ[d.Ω] d.Ω ⊗[K] T).toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom
  have hψφ (y : baseChange (K := L) A) :
      Bialgebra.counitAlgHom d.Ω (d.Ω ⊗[K] T) (φ y) =
        d.right (Bialgebra.counitAlgHom L (baseChange (K := L) A) y) := by
    simp [φ, Bialgebra.counitAlgHom_apply, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have hconn : ConnectedSpace (PrimeSpectrum (d.Ω ⊗[K] T)) :=
    (hT.baseChange K d.Ω T).connectedSpace
  -- `φ` pulls the augmentation point back to the augmentation point, since it commutes with the
  -- counits up to the injection `d.right`.
  have hz : PrimeSpectrum.comap φ (Bialgebra.augmentationPoint d.Ω (d.Ω ⊗[K] T)) =
      Bialgebra.augmentationPoint L (baseChange (K := L) A) :=
    AlgHom.comap_kernelPoint_of_apply_eq _ _ φ (d.right : L →+* d.Ω) d.right.injective hψφ
  rw [HopfAlgebra.mem_identityComponentHopfIdeal, ← hz] at hx
  have h₁ : φ (1 ⊗ₜ x) = (1 : d.Ω) ⊗ₜ[K] g.hom (1 ⊗ₜ x) := by
    simp [φ, e]
  have h₂ : φ (1 ⊗ₜ x) = 0 := PrimeSpectrum.connectedComponentIdeal_comap_le_ker φ _ hx
  exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff K T _).mp (h₁.symm.trans h₂)

/-- **Descent of the geometric identity component.** Let `k` be a perfect field and `A` the
coordinate Hopf algebra of an affine group `G` of finite type over `k`. There is a unique Hopf
ideal of `A` whose base change to `AlgebraicClosure k` cuts out the identity component of
`G_{k^alg}`: the identity component is defined over `k`. -/
theorem existsUnique_baseChangeHopfIdeal_eq_identityComponentHopfIdeal
    {k : Type u} [Field k] [PerfectField k] {A : _root_.CommHopfAlgCat.{v} k}
    [Algebra.FiniteType k A] :
    ∃! I : HopfIdeal k A, baseChangeHopfIdeal (K := AlgebraicClosure k) I =
      HopfAlgebra.identityComponentHopfIdeal (k := AlgebraicClosure k)
        (H := baseChange (K := AlgebraicClosure k) A) := by
  have : IsGalois k (AlgebraicClosure k) := {}
  exact (existsUnique_baseChangeHopfIdeal_eq_iff _).mpr
    fun σ _ hx ↦ (map_mem_identityComponentHopfIdeal_baseChange_iff σ).mpr hx

/-- **Groups generated by connected groups are connected.** Let `k` be a perfect field, `K / k`
a field extension, `G` an affine group over `k` with coordinate Hopf algebra `H`, and
`f i : M_i → G_K` a family of homomorphisms from geometrically connected affine groups over `K`.
The smallest closed `k`-subgroup of `G` through whose base change to `K` every `f i` factors, cut
out by `contractHopfIdeal (commonKernelHopfIdeal f)`, is geometrically connected when it is of
finite type. -/
theorem geometricallyConnectedCommHopfAlgProperty_quotient_contractHopfIdeal_commonKernelHopfIdeal
    {k : Type u} {K : Type u'} [Field k] [PerfectField k] [Field K] [Algebra k K]
    {H : _root_.CommHopfAlgCat.{v} k} {ι : Type*} {T : ι → _root_.CommHopfAlgCat.{max u' v} K}
    (f : ∀ i, baseChange (K := K) H ⟶ T i)
    (hT : ∀ i, geometricallyConnectedCommHopfAlgProperty K (T i))
    [Algebra.FiniteType k (quotient H (contractHopfIdeal (commonKernelHopfIdeal f)))] :
    geometricallyConnectedCommHopfAlgProperty k
      (quotient H (contractHopfIdeal (commonKernelHopfIdeal f))) := by
  set J := contractHopfIdeal (commonKernelHopfIdeal f)
  let L := AlgebraicClosure k
  let E : HopfIdeal L (baseChange (K := L) (quotient H J)) :=
    HopfAlgebra.identityComponentHopfIdeal
  obtain ⟨I, hI, -⟩ : ∃! I : HopfIdeal k (quotient H J), baseChangeHopfIdeal (K := L) I = E :=
    existsUnique_baseChangeHopfIdeal_eq_identityComponentHopfIdeal
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
    rw [baseChangeMap_apply_tmul] at hcomp
    rw [Ideal.mem_comap, RingHom.mem_ker]
    simpa only [AlgHom.toRingHom_eq_coe, Algebra.TensorProduct.includeRight_apply,
      RingHom.coe_coe, BialgHom.coe_toAlgHom, ← hcomp] using
      apply_one_tmul_eq_zero_of_mem_identityComponentHopfIdeal (hT i)
      (baseChangeLiftQuotient J (f i) (hf i)) hmem
  have hE : E = ⊥ := by rw [← hI, eq_bot_of_comapOfSurjective_le I hI'J, baseChangeHopfIdeal_bot]
  rw [geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_baseChange k L]
  exact HopfAlgebra.identityComponentHopfIdeal_eq_bot_iff_connectedSpace.mp hE

end TauCeti.CommHopfAlgCat
