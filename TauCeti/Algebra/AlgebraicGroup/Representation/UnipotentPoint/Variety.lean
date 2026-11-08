/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Ideal
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.HopfAlgebra.Antipode
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# The defining ideal of the unipotent variety

Let `G = Spec H` be an affine group over a field `k`. The **unipotent variety** of `G` is the
reduced closed subscheme of `G` supported on the geometric unipotent points. This file defines its
ideal `I_U ⊆ H` intrinsically, as the ideal of functions vanishing at every unipotent point with
values in the algebraic closure of `k`, without choosing a representation. The unipotent variety
is then `Spec (H ⧸ I_U)`, and its points with values in a `k`-algebra `B` are the points
`H →ₐ[k] B` annihilating `I_U`. Over a nonreduced `B` this is a genuine condition on the whole
ideal: it is not the condition that some faithful representation `ρ` makes `ρ(g) - 1` nilpotent,
nor the vanishing of the characteristic-polynomial equations of `ρ` alone.

When `H` is of finite type, `I_U` is the radical of the unipotence ideal `J_ρ` of every faithful
finite-dimensional representation `ρ`, it may be computed with the unipotent points valued in any
algebraically closed extension of `k`, and its points with values in a perfect field are exactly
the unipotent points.

The unipotent variety contains the identity, is stable under inversion, and every homomorphism of
affine groups maps it into the unipotent variety of the target. On coordinate rings, these are the
containments `I_U ≤ ker ε`, `S⁻¹(I_U) = I_U` for the antipode `S`, and `I_U ≤ f⁻¹(I_U')` for a
bialgebra morphism `f : H → H'`. Feeding the last two into `Ideal.quotientMapₐ` gives the inversion
of the unipotent variety and the morphisms between unipotent varieties on coordinate rings.

## Main declarations

* `TauCeti.HopfAlgebra.unipotentVarietyIdeal`: the ideal of the unipotent variety.
* `TauCeti.HopfAlgebra.unipotentVarietyIdeal_isRadical`: it is a radical ideal, so the unipotent
  variety is reduced.
* `TauCeti.HopfAlgebra.radical_unipotenceIdeal_eq_unipotentVarietyIdeal`: it is the radical of the
  unipotence ideal of any faithful representation.
* `TauCeti.HopfAlgebra.mem_unipotentVarietyIdeal_iff_of_isAlgClosed`: it may be computed with the
  unipotent points valued in any algebraically closed extension.
* `TauCeti.HopfAlgebra.unipotentVarietyIdeal_le_ker_iff`: its points with values in a perfect
  field are the unipotent points.
* `TauCeti.HopfAlgebra.comap_antipodeAlgHom_unipotentVarietyIdeal`: stability under inversion.
* `TauCeti.HopfAlgebra.unipotentVarietyIdeal_le_comap`: functoriality along homomorphisms of
  affine groups.

## References

* A. Borel, *Linear Algebraic Groups*, §4.4 and §4.8.
* A. Bertoloni Meli, N. Imai and A. Youcis, *The Jacobson–Morozov morphism for Langlands
  parameters in the relative setting*, §2.1, Proposition 2.3.
-/

public section

namespace TauCeti.HopfAlgebra

universe u v w

noncomputable section

section Field

variable (k : Type u) (H : Type v) [Field k] [CommRing H] [_root_.HopfAlgebra k H]

/-- The **ideal of the unipotent variety** of the affine group `Spec H` over a field `k`: the
functions vanishing at every unipotent point with values in the algebraic closure of `k`. Over a
finite-type `H` it is the radical of the unipotence ideal of any faithful representation
(`radical_unipotenceIdeal_eq_unipotentVarietyIdeal`), and the algebraic closure may be replaced by
any algebraically closed extension (`mem_unipotentVarietyIdeal_iff_of_isAlgClosed`). -/
def unipotentVarietyIdeal : Ideal H :=
  ⨅ g : {g : WithConv (H →ₐ[k] AlgebraicClosure k) // IsUnipotentPoint g},
    RingHom.ker (g : WithConv (H →ₐ[k] AlgebraicClosure k)).ofConv

variable {k H}

/-- A function lies in the ideal of the unipotent variety exactly when it vanishes at every
unipotent point with values in the algebraic closure. -/
theorem mem_unipotentVarietyIdeal_iff (x : H) :
    x ∈ unipotentVarietyIdeal k H ↔
      ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k), IsUnipotentPoint g → g.ofConv x = 0 := by
  simp [unipotentVarietyIdeal, RingHom.mem_ker]

/-- The ideal of the unipotent variety is radical, as an intersection of kernels of points valued
in a field. -/
theorem unipotentVarietyIdeal_isRadical : (unipotentVarietyIdeal k H).IsRadical :=
  Ideal.isRadical_iInf _ fun _ ↦ (RingHom.ker_isPrime _).isRadical

/-- The ideal of the unipotent variety is its own radical. -/
@[simp]
theorem radical_unipotentVarietyIdeal :
    (unipotentVarietyIdeal k H).radical = unipotentVarietyIdeal k H :=
  unipotentVarietyIdeal_isRadical.radical

/-- The coordinate ring of the unipotent variety is reduced. -/
instance : IsReduced (H ⧸ unipotentVarietyIdeal k H) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp unipotentVarietyIdeal_isRadical

/-- The unipotent variety contains the identity: its ideal is contained in the kernel of the
counit. -/
theorem unipotentVarietyIdeal_le_ker_counitAlgHom :
    unipotentVarietyIdeal k H ≤ RingHom.ker (Bialgebra.counitAlgHom k H) := by
  intro x hx
  have h := (mem_unipotentVarietyIdeal_iff x).mp hx 1 isUnipotentPoint_one
  rw [AlgHom.convOne_apply] at h
  simpa using h

/-- The unipotent variety is stable under inversion: a function lies in its ideal exactly when its
image under the antipode does. -/
@[simp]
theorem antipode_mem_unipotentVarietyIdeal_iff (x : H) :
    HopfAlgebraStruct.antipode k x ∈ unipotentVarietyIdeal k H ↔
      x ∈ unipotentVarietyIdeal k H := by
  have key : ∀ y : H, y ∈ unipotentVarietyIdeal k H →
      HopfAlgebraStruct.antipode k y ∈ unipotentVarietyIdeal k H := by
    intro y hy
    rw [mem_unipotentVarietyIdeal_iff] at hy ⊢
    intro g hg
    rw [← WithConv.algHom_inv_apply]
    exact hy g⁻¹ hg.inv
  refine ⟨fun hx ↦ ?_, key x⟩
  simpa using key _ hx

/-- The antipode pulls the ideal of the unipotent variety back to itself. This is the equation of
the inversion of the unipotent variety on its coordinate ring. -/
@[simp]
theorem comap_antipodeAlgHom_unipotentVarietyIdeal :
    (unipotentVarietyIdeal k H).comap (_root_.HopfAlgebra.antipodeAlgHom k H) =
      unipotentVarietyIdeal k H := by
  ext x
  simp

/-- A homomorphism of affine groups maps unipotent varieties into unipotent varieties. For a
bialgebra morphism `f : H → H'`, the induced homomorphism `Spec H' → Spec H` maps the unipotent
variety of `Spec H'` into that of `Spec H`: on coordinate rings, `f` pulls the ideal of the
unipotent variety of `Spec H'` back to an ideal containing that of `Spec H`. -/
theorem unipotentVarietyIdeal_le_comap {H' : Type w} [CommRing H'] [_root_.HopfAlgebra k H']
    (f : H →ₐc[k] H') :
    unipotentVarietyIdeal k H ≤ (unipotentVarietyIdeal k H').comap (f : H →ₐ[k] H') := by
  intro x hx
  rw [Ideal.mem_comap, mem_unipotentVarietyIdeal_iff]
  intro g hg
  have h := (mem_unipotentVarietyIdeal_iff x).mp hx _ (hg.mapDomain f)
  rwa [BialgHom.mapDomain_apply, WithConv.ofConv_toConv, AlgHom.comp_apply] at h

/-- An isomorphism of affine groups identifies their unipotent varieties. -/
@[simp]
theorem comap_unipotentVarietyIdeal_bialgEquiv {H' : Type w} [CommRing H']
    [_root_.HopfAlgebra k H'] (e : H ≃ₐc[k] H') :
    (unipotentVarietyIdeal k H').comap (e : H →ₐ[k] H') = unipotentVarietyIdeal k H := by
  refine le_antisymm (fun x hx ↦ ?_) (unipotentVarietyIdeal_le_comap (e : H →ₐc[k] H'))
  rw [Ideal.mem_comap, mem_unipotentVarietyIdeal_iff] at hx
  rw [mem_unipotentVarietyIdeal_iff]
  intro g hg
  obtain ⟨g', rfl⟩ := (BialgEquiv.mapDomainMulEquiv (A := AlgebraicClosure k) e).surjective g
  rw [BialgEquiv.mapDomainMulEquiv_apply] at hg ⊢
  rw [BialgHom.mapDomain_apply_apply]
  exact hx g' ((isUnipotentPoint_mapDomain_iff e g').mp hg)

end Field

section FiniteType

variable {k H : Type u} [Field k] [CommRing H] [_root_.HopfAlgebra k H] [Algebra.FiniteType k H]

/-- **The unipotent variety is cut out by any faithful representation up to radical.** For a
faithful finite-dimensional representation `M`, the radical of its unipotence ideal is the ideal
of the unipotent variety. -/
theorem radical_unipotenceIdeal_eq_unipotentVarietyIdeal (M : FGComoduleCat.{u, u, u} k H)
    (hM : Comodule.IsFaithful (k := k) (H := H) (V := M)) :
    (Comodule.unipotenceIdeal k H M).radical = unipotentVarietyIdeal k H := by
  ext x
  rw [Comodule.mem_radical_unipotenceIdeal_iff (AlgebraicClosure k) M hM,
    mem_unipotentVarietyIdeal_iff]

/-- The ideal of the unipotent variety may be computed with the unipotent points valued in any
algebraically closed extension of the ground field. -/
theorem mem_unipotentVarietyIdeal_iff_of_isAlgClosed (K : Type u) [Field K] [Algebra k K]
    [IsAlgClosed K] (x : H) :
    x ∈ unipotentVarietyIdeal k H ↔
      ∀ g : WithConv (H →ₐ[k] K), IsUnipotentPoint g → g.ofConv x = 0 := by
  obtain ⟨M, hM⟩ := Comodule.exists_isFaithful (k := k) (H := H)
  rw [← radical_unipotenceIdeal_eq_unipotentVarietyIdeal M hM,
    Comodule.mem_radical_unipotenceIdeal_iff K M hM]

/-- The points of the unipotent variety with values in a perfect field are exactly the unipotent
points. -/
theorem unipotentVarietyIdeal_le_ker_iff {K : Type u} [Field K] [Algebra k K] [PerfectField K]
    (g : WithConv (H →ₐ[k] K)) :
    unipotentVarietyIdeal k H ≤ RingHom.ker g.ofConv ↔ IsUnipotentPoint g := by
  obtain ⟨M, hM⟩ := Comodule.exists_isFaithful (k := k) (H := H)
  rw [← radical_unipotenceIdeal_eq_unipotentVarietyIdeal M hM,
    Comodule.radical_unipotenceIdeal_le_ker_iff_isUnipotentPoint M hM]

end FiniteType

end

end TauCeti.HopfAlgebra
