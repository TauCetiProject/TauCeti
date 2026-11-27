/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.QuasiIso
public import TauCeti.AlgebraicTopology.DGLocalSystem.LoopAlgebra
public import TauCeti.AlgebraicTopology.DGLocalSystem.MarkedEvaluation

/-!
# Continuation maps over the loop chains with unit diagonal in the group ring

Let `ν` be a continuation cocycle over the chain algebra `C_*(Ω_x X; R)` of the Moore loops,
between two twisting cocycles on the same generators, which vanishes between distinct generators
of equal index. If the diagonal entry `ν a a` of each generator goes to a unit of the group ring
`R[π₁(X, x)] = H₀(Ω_x X; R)` under `TauCeti.loopChainToGroupAlgebra`, then the continuation map of
`ν` is a quasi-isomorphism of twisted complexes, for every DG right module over `C_*(Ω_x X; R)`
(`TauCeti.ContinuationCocycle.quasiIso_continuationHom_of_isUnit_loopChainToGroupAlgebra`). So
twisting by the two cocycles gives the same cohomology.

This covers the continuation cocycles whose diagonal entries are point chains of loops, which are
units of the group ring but, for loops of positive length, not of the chain algebra: such a
cocycle need not be invertible as a matrix, so `TauCeti.ContinuationCocycle.continuationIsoOfIsUnit`
does not apply. A diagonal entry whose image in the group ring is a unit is invertible up to
homotopy (`TauCeti.exists_cubicalChainDifferential_eq_mul_sub_one_of_isUnit`), and the algebra
of the chains on a based loop space is concentrated in nonpositive cohomological degrees, so
`TauCeti.ContinuationCocycle.quasiIso_continuationHom_of_nonpos` applies.

The continuation cocycle of a homotopy between two collapse maps
(`TauCeti.TwistingChainSystem.MarkedHomotopy.mooreHomotopyCocycle`) is of this kind: its diagonal
entries are the point chains of the tracks of the homotopy, plus the push-forwards of the chains of
a marked homotopy. When the spaces of the twisting chain system are empty between elements of
equal index, as the trajectory spaces of a Morse–Smale pair are, those chains vanish there, so
its continuation map is a quasi-isomorphism
(`TauCeti.TwistingChainSystem.MarkedHomotopy.quasiIso_continuationHom_mooreHomotopyCocycle`):
changing the collapse map does not change the twisted cohomology.

## Main results

* `TauCeti.ContinuationCocycle.quasiIso_continuationHom_of_isUnit_loopChainToGroupAlgebra`: a
  continuation cocycle over the loop chains whose diagonal entries are units in the group ring
  induces quasi-isomorphisms of twisted complexes.
* `TauCeti.TwistingChainSystem.MarkedHomotopy.mooreHomotopyCocycle_ν_eq_zero_of_ne`: the
  continuation cocycle of a homotopy of collapse maps vanishes off the diagonal where the space is
  empty.
* `TwistingChainSystem.MarkedHomotopy.isUnit_loopChainToGroupAlgebra_mooreHomotopyCocycle_ν`:
  its diagonal entries are units in the group ring where the space is empty.
* `TauCeti.TwistingChainSystem.MarkedHomotopy.quasiIso_continuationHom_mooreHomotopyCocycle`: the
  continuation map of a homotopy of collapse maps is a quasi-isomorphism when the spaces are
  empty between elements of equal index.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 6.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §§1.4 and 2.2.
-/

public section

namespace TauCeti

universe u uM uP

namespace ContinuationCocycle

variable {X : Type u} [TopologicalSpace X] {x : X} {R : Type u} [CommRing R]
  {M : Type uM} [AddCommGroup M] [Module R M] [Module (loopChainAlgebra X x R)ᵐᵒᵖ M]
  [IsScalarTower R (loopChainAlgebra X x R)ᵐᵒᵖ M] [SMulCommClass R (loopChainAlgebra X x R)ᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul
    (InternalGrading.ofDecomposition (cubicalChainGrading (MooreLoopSpace X x) R)).opposite.piece
    ℳ]
  {dM : M →ₗ[R] M} {P : Type uP} [Fintype P] {ind : P → ℤ}
  {m₁ m₂ : TwistingCocycle (R := R) (A := loopChainAlgebra X x R)
    (cubicalChainGrading (MooreLoopSpace X x) R) (cubicalChainDifferential (MooreLoopSpace X x) R)
    P ind}

/-- **A continuation cocycle over the loop chains whose diagonal is a unit in the group ring
induces quasi-isomorphisms.** Let `ν` be a continuation cocycle over `C_*(Ω_x X; R)` between
twisting cocycles on the same generators, vanishing between distinct generators of equal index,
whose diagonal entries go to units of `R[π₁(X, x)]`. Then for every differential graded right
module over `C_*(Ω_x X; R)` its continuation map is a quasi-isomorphism of twisted complexes. -/
theorem quasiIso_continuationHom_of_isUnit_loopChainToGroupAlgebra (ν : ContinuationCocycle m₁ m₂)
    (hν : ∀ a b, ind a = ind b → a ≠ b → ν.ν a b = 0)
    (hunit : ∀ a, IsUnit (loopChainToGroupAlgebra X x R (ν.ν a a)))
    (hM : IsDGRightModule (loopChain_isDGAlgebra X x R) ℳ dM) :
    QuasiIso (ν.continuationHom hM) :=
  ν.quasiIso_continuationHom_of_nonpos (fun _ hn ↦ cubicalChainGrading_eq_bot _ R hn) hν
    (fun a ↦ exists_cubicalChainDifferential_eq_mul_sub_one_of_isUnit
      (by simpa using ν.mem_graded a a) (hunit a)) hM

end ContinuationCocycle

/-! ### Changing the collapse map -/

namespace TwistingChainSystem.MarkedHomotopy

variable {P : Type uP} [Fintype P] [DecidableEq P] {ind : P → ℤ} {M : P → P → Type*}
  [∀ x y, TopologicalSpace (M x y)] {B : Type*} [TopologicalSpace B]
  {e : ∀ x y, C(M x y, MoorePath B)} {ι : ∀ x y z, C(M x y × M y z, M x z)}
  {X : Type u} [TopologicalSpace X] {x₀ : X} {c : P → B}
  {he₀ : ∀ x y u, (e x y u).source = c x} {he₁ : ∀ x y u, (e x y u).target = c y}
  {he : ∀ x z y u v, e x y (ι x z y (u, v)) =
    (e x z u).trans (e z y v) ((he₁ x z u).trans (he₀ z y v).symm)}
  {θ₀ θ₁ : C(B, X)} (hθ₀ : ∀ x, θ₀ (c x) = x₀) (hθ₁ : ∀ x, θ₁ (c x) = x₀) (H : θ₀.Homotopy θ₁)
  {R : Type u} [CommRing R] {S : TwistingChainSystem ind ι R}
  {N : Type uM} [AddCommGroup N] [Module R N] [Module (loopChainAlgebra X x₀ R)ᵐᵒᵖ N]
  [IsScalarTower R (loopChainAlgebra X x₀ R)ᵐᵒᵖ N] [SMulCommClass R (loopChainAlgebra X x₀ R)ᵐᵒᵖ N]
  {𝒩 : ℤ → Submodule R N} [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul
    (InternalGrading.ofDecomposition (cubicalChainGrading (MooreLoopSpace X x₀) R)).opposite.piece
    𝒩]
  {dN : N →ₗ[R] N}

/-- Off the diagonal, the continuation cocycle of a homotopy `H` between two collapse maps vanishes
wherever the space `M x y` of the twisting chain system is empty: the marked space is then empty,
so the chain of the marked homotopy `T` vanishes. -/
theorem mooreHomotopyCocycle_ν_eq_zero_of_ne
    (T : S.MarkedHomotopy (length_eq_add_of_eq_trans he₀ he₁ he)) {x y : P} (hM : IsEmpty (M x y))
    (hne : x ≠ y) : (T.mooreHomotopyCocycle he₀ he₁ he hθ₀ hθ₁ H).ν x y = 0 := by
  have : IsEmpty (markedSpace e x y) := ⟨fun p ↦ isEmptyElim p.val.1⟩
  rw [mooreHomotopyCocycle_ν, Matrix.diagonal_apply_ne _ hne, zero_add,
    Subsingleton.elim (T.chain x y) 0, map_zero]

/-- The diagonal entry at `x` of the continuation cocycle of a homotopy `H` between two collapse
maps is a unit of the group ring `R[π₁(X, x₀)]` when the space `M x x` of the twisting chain system
is empty: it is then the point chain of the track of `H` at `x`, a loop at `x₀`. -/
theorem isUnit_loopChainToGroupAlgebra_mooreHomotopyCocycle_ν
    (T : S.MarkedHomotopy (length_eq_add_of_eq_trans he₀ he₁ he)) {x : P} (hM : IsEmpty (M x x)) :
    IsUnit (loopChainToGroupAlgebra X x₀ R
      ((T.mooreHomotopyCocycle he₀ he₁ he hθ₀ hθ₁ H).ν x x)) := by
  have : IsEmpty (markedSpace e x x) := ⟨fun p ↦ isEmptyElim p.val.1⟩
  rw [mooreHomotopyCocycle_ν, Matrix.diagonal_apply_eq, Subsingleton.elim (T.chain x x) 0, map_zero,
    add_zero, loopChainToGroupAlgebra_cubicalChainPoint, ← MonoidAlgebra.of_apply]
  exact (Group.isUnit _).map _

/-- **Changing the collapse map does not change the twisted cohomology.** Let `T` be a marked
homotopy of a twisting chain system `S` whose spaces `M x y` are empty between elements of equal
index, as the trajectory spaces of a Morse–Smale pair are. Then the continuation cocycle of a
homotopy `H` between two collapse maps `θ₀` and `θ₁` induces quasi-isomorphisms between the twisted
complexes of the twisting cocycles of `S` over the Moore loops for `θ₀` and for `θ₁`, for every
differential graded right module over `C_*(Ω_{x₀} X; R)`. Its diagonal entries are the point chains
of the tracks of `H`, which are units of the group ring `R[π₁(X, x₀)]` but, for tracks of positive
length, not of the chain algebra. -/
theorem quasiIso_continuationHom_mooreHomotopyCocycle
    (hM : ∀ x y, ind x = ind y → IsEmpty (M x y))
    (T : S.MarkedHomotopy (length_eq_add_of_eq_trans he₀ he₁ he))
    (hN : IsDGRightModule (loopChain_isDGAlgebra X x₀ R) 𝒩 dN) :
    QuasiIso ((T.mooreHomotopyCocycle he₀ he₁ he hθ₀ hθ₁ H).continuationHom hN) :=
  ContinuationCocycle.quasiIso_continuationHom_of_isUnit_loopChainToGroupAlgebra _
    (fun x y hxy ↦ mooreHomotopyCocycle_ν_eq_zero_of_ne hθ₀ hθ₁ H T (hM x y hxy))
    (fun x ↦ isUnit_loopChainToGroupAlgebra_mooreHomotopyCocycle_ν hθ₀ hθ₁ H T (hM x x rfl)) hN

end TwistingChainSystem.MarkedHomotopy

end TauCeti
