/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic
public import TauCeti.Algebra.AlgebraicGroup.LinearlyReductive
import Mathlib.LinearAlgebra.Projection
import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Hom
import TauCeti.Algebra.Coalgebra.Subcomodule.PointSeparation
import TauCeti.RepresentationTheory.RelativeNorm

/-!
# Lifting linear reductivity from finite-index subgroups

Let `H₁` be a reduced, finite-type commutative Hopf algebra over an algebraically closed field `k`,
and let `f : H₁ →ₐc[k] H₂` be a bialgebra homomorphism into a Hopf algebra `H₂` such that the
image `N` of `H₂(k) → H₁(k)` has finite index invertible in `k`. If a comodule `M` over `H₁`
becomes completely reducible upon corestriction along `f`, then `M` is already completely reducible
over `H₁`. Consequently, linear reductivity of `H₂` lifts to `H₁`.

The argument is Maschke averaging over left cosets `H₁(k) / N`. Given an `H₁`-subcomodule `W` of
`M`, complete reducibility of the corestricted comodule supplies an `H₂`-comodule projection `π`
onto `W`, which commutes with the action of every point in `N`. Applying the relative norm
`Representation.relNorm` to the conjugation action of `H₁(k)` on `Module.End k M` averages `π`
over a left transversal of `N`; normalizing by `[H₁(k) : N]⁻¹` produces an `H₁(k)`-equivariant
linear projection onto `W`. Its kernel is an `H₁(k)`-stable complement of `W`, and geometric point
separation for the reduced finite-type coordinate algebra `H₁` promotes that kernel to an
`H₁`-subcomodule complement.

No normality hypothesis on the subgroup `N` and no reducedness or finite-type hypothesis on `H₂`
are needed. Specializing `f` to a Hopf-ideal quotient morphism lifts linear reductivity from any
closed subgroup whose rational points have finite index prime to the characteristic.

## Main declarations

* `TauCeti.Comodule.isCompletelyReducible_of_corestrict_finiteIndex`: lifting complete reducibility
  of an individual comodule along a bialgebra morphism whose image on rational points has finite
  index invertible in `k`.
* `TauCeti.Coalgebra.IsLinearlyReductive.of_bialgHom_finiteIndex`: lifting linear reductivity along
  such a bialgebra morphism.
* `TauCeti.linearlyReductiveCommHopfAlgProperty.of_finiteIndex`: the bundled categorical form.
* `TauCeti.linearlyReductiveCommHopfAlgProperty.of_quotient_finiteIndex`: lifting linear
  reductivity from a Hopf-ideal quotient whose rational-point subgroup has finite index invertible
  in `k`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Corollary 22.43.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti

universe u v v' w

section Unbundled

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H₁ : Type v} [CommRing H₁] [_root_.HopfAlgebra k H₁]
  [Algebra.FiniteType k H₁] [IsReduced H₁]
variable {H₂ : Type v'} [Semiring H₂] [_root_.HopfAlgebra k H₂]

/-- **Finite-index lifting of complete reducibility.** Over an algebraically closed field `k`, let
`H₁` be a reduced, finite-type coordinate Hopf algebra and `f : H₁ →ₐc[k] H₂` a bialgebra morphism
whose image on `k`-points has index nonzero in `k` (in particular, finite index). If an
`H₁`-comodule `M` is completely reducible after corestriction along `f`, then `M` is completely
reducible over `H₁`. -/
theorem Comodule.isCompletelyReducible_of_corestrict_finiteIndex
    (f : H₁ →ₐc[k] H₂)
    (hindex : ((BialgHom.mapDomain (A := k) f).range.index : k) ≠ 0)
    {M : Type w} [AddCommMonoid M] [Module k M] [Comodule k H₁ M]
    (hM : letI : Comodule k H₂ M := Comodule.Corestrict f.toCoalgHom
      Comodule.IsCompletelyReducible k H₂ M) :
    Comodule.IsCompletelyReducible k H₁ M := by
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let _ : Comodule k H₂ M := Comodule.Corestrict f.toCoalgHom
  let N : Subgroup (WithConv (H₁ →ₐ[k] k)) := (BialgHom.mapDomain (A := k) f).range
  have hindex' : (N.index : k) ≠ 0 := hindex
  have hfin : Finite (WithConv (H₁ →ₐ[k] k) ⧸ N) :=
    Nat.finite_of_card_ne_zero fun h ↦ hindex' (by rw [Subgroup.index_eq_card, h, Nat.cast_zero])
  have _ : Fintype (WithConv (H₁ →ₐ[k] k) ⧸ N) := Fintype.ofFinite _
  let ρ : Representation k (WithConv (H₁ →ₐ[k] k)) M :=
    Comodule.basePointsRepresentation (R := k) (H := H₁) M
  refine Comodule.IsCompletelyReducible.of_exists_isCompl fun W ↦ ?_
  obtain ⟨Q, hWQ⟩ := hM.exists_isCompl (W.corestrict f.toCoalgHom)
  let πHom : Comodule.Hom k H₂ M M := Subcomodule.projection (W.corestrict f.toCoalgHom) Q hWQ
  let π : M →ₗ[k] M := πHom.toLinearMap
  have hπ_mem (m : M) : π m ∈ W.toSubmodule :=
    (Subcomodule.mem_corestrict f.toCoalgHom W _).mp (Subcomodule.projection_apply_mem hWQ m)
  have hπ_left {m : M} (hm : m ∈ W.toSubmodule) : π m = m :=
    Subcomodule.projection_apply_of_mem_left hWQ
      ((Subcomodule.mem_corestrict f.toCoalgHom W m).mpr hm)
  have hπ_comm (n : N) (x : M) :
      π (ρ (n : WithConv (H₁ →ₐ[k] k)) x) = ρ (n : WithConv (H₁ →ₐ[k] k)) (π x) := by
    obtain ⟨g, hg⟩ := n.property
    have hcore := congrArg (fun l : M →ₗ[k] M ↦ l x)
      (Comodule.basePointsRepresentation_corestrict (R := k) (M := M) f g)
    have hcore' := congrArg (fun l : M →ₗ[k] M ↦ l (π x))
      (Comodule.basePointsRepresentation_corestrict (R := k) (M := M) f g)
    rw [← hg, ← hcore, ← hcore']
    exact πHom.map_basePointsRepresentation g x
  have hW_stable (g : WithConv (H₁ →ₐ[k] k)) {m : M} (hm : m ∈ W.toSubmodule) :
      ρ g m ∈ W.toSubmodule :=
    Comodule.basePointsRepresentation_mem W g hm
  -- Average the `N`-equivariant projection `π` over a left transversal of `N` using `relNorm`.
  let P : M →ₗ[k] M := (N.index : k)⁻¹ • Representation.relNorm (Representation.linHom ρ ρ) N π
  have hP_comm (g : WithConv (H₁ →ₐ[k] k)) (m : M) : P (ρ g m) = ρ g (P m) := by
    simp only [P, LinearMap.smul_apply, Representation.relNorm_linHom_apply_comm ρ ρ hπ_comm,
      map_smul]
  have hP_mem (m : M) : P m ∈ W.toSubmodule :=
    Submodule.smul_mem _ _ (Representation.relNorm_linHom_mem ρ (fun g _ ↦ hW_stable g) hπ_mem m)
  have hP_left {m : M} (hm : m ∈ W.toSubmodule) : P m = m := by
    simp only [P, LinearMap.smul_apply,
      Representation.relNorm_linHom_apply_of_mem ρ (fun g _ ↦ hW_stable g) (fun _ ↦ hπ_left) hm,
      ← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hindex', one_smul]
  have hker_stable : ∀ (g : H₁ →ₐ[k] k) {m : M}, m ∈ LinearMap.ker P →
      Comodule.endOfPoint M g ((1 : k) ⊗ₜ[k] m) ∈ (LinearMap.ker P).baseChange k := by
    intro g m hm
    rw [Comodule.endOfPoint_tmul, one_smul,
      Comodule.endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation]
    refine Submodule.tmul_mem_baseChange_of_mem _ ?_
    have hcomm_g := hP_comm (toConv g) m
    rw [LinearMap.mem_ker, hcomm_g, LinearMap.mem_ker.mp hm, map_zero]
  refine ⟨Subcomodule.ofEndOfPointStable (K := k) (LinearMap.ker P) hker_stable, ?_⟩
  rw [Subcomodule.ofEndOfPointStable_toSubmodule]
  exact (⟨hP_mem, fun _ hm ↦ hP_left hm⟩ : LinearMap.IsProj W.toSubmodule P).isCompl

/-- **Finite-index lifting of linear reductivity.** Over an algebraically closed field `k`, if a
bialgebra morphism `f : H₁ →ₐc[k] H₂` from a reduced finite-type commutative Hopf algebra `H₁`
has rational-point image of index nonzero in `k` and `H₂` is linearly reductive, then `H₁` is
linearly reductive. -/
theorem Coalgebra.IsLinearlyReductive.of_bialgHom_finiteIndex
    (f : H₁ →ₐc[k] H₂)
    (hindex : ((BialgHom.mapDomain (A := k) f).range.index : k) ≠ 0)
    (hH₂ : Coalgebra.IsLinearlyReductive.{u, v', w} k H₂) :
    Coalgebra.IsLinearlyReductive.{u, v, w} k H₁ := by
  refine Coalgebra.IsLinearlyReductive.of_forall_isCompletelyReducible k fun M _ _ _ _ ↦ ?_
  refine Comodule.isCompletelyReducible_of_corestrict_finiteIndex f hindex ?_
  let _ : Comodule k H₂ M := Comodule.Corestrict f.toCoalgHom
  exact hH₂.isCompletelyReducible_same_universe k M

end Unbundled

section Bundled

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Bundled form of `Coalgebra.IsLinearlyReductive.of_bialgHom_finiteIndex`: linear reductivity
lifts along a coordinate morphism of commutative Hopf algebras whose domain is reduced and of
finite type and whose image on rational points has index nonzero in `k`. -/
theorem linearlyReductiveCommHopfAlgProperty.of_finiteIndex
    {H₁ H₂ : _root_.CommHopfAlgCat.{v} k} [Algebra.FiniteType k H₁] [IsReduced H₁]
    (f : H₁ ⟶ H₂)
    (hindex : ((BialgHom.mapDomain (A := k) f.hom).range.index : k) ≠ 0)
    (hH₂ : linearlyReductiveCommHopfAlgProperty k H₂) :
    linearlyReductiveCommHopfAlgProperty k H₁ :=
  (linearlyReductiveCommHopfAlgProperty_iff k H₁).mpr <|
    Coalgebra.IsLinearlyReductive.of_bialgHom_finiteIndex f.hom hindex
      ((linearlyReductiveCommHopfAlgProperty_iff k H₂).mp hH₂)

/-- Over an algebraically closed field `k`, a reduced finite-type affine group is linearly reductive
whenever it has a linearly reductive closed subgroup whose rational points have index nonzero
in `k`. -/
theorem linearlyReductiveCommHopfAlgProperty.of_quotient_finiteIndex
    {H : _root_.CommHopfAlgCat.{v} k} [Algebra.FiniteType k H] [IsReduced H]
    (I : HopfIdeal k H)
    (hindex : ((CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k k)).index : k) ≠ 0)
    (hQ : linearlyReductiveCommHopfAlgProperty k (CommHopfAlgCat.quotient H I)) :
    linearlyReductiveCommHopfAlgProperty k H := by
  have hrange : (BialgHom.mapDomain (A := k) (CommHopfAlgCat.mkQuotient H I).hom).range =
      CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k k) :=
    congrArg MonoidHom.range (MonoidHom.ext fun f ↦ by
      rw [BialgHom.mapDomain_apply]
      exact (CommHopfAlgCat.quotientPointsHom_apply H I (CommAlgCat.of k k) f).symm)
  refine linearlyReductiveCommHopfAlgProperty.of_finiteIndex
    (CommHopfAlgCat.mkQuotient H I) ?_ hQ
  rwa [hrange]

end Bundled

end TauCeti
