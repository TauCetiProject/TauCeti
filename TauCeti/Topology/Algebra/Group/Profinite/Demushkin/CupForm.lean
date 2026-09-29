/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialFp.Form
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Basic
import Mathlib.Algebra.CharP.Reduced
import Mathlib.RingTheory.SimpleModule.Rank

/-!
# The cup form of a Demushkin group and its normal forms

For a Demushkin group `G`, `H²(G, 𝔽_p)` is one-dimensional, so a nonzero linear functional
`φ : H²(G, 𝔽_p) →ₗ 𝔽_p` is an isomorphism, and the cup form `φ.cupForm`, the bilinear form
`(a, b) ↦ φ (a ⌣ b)` on `H¹(G, 𝔽_p)`, is nondegenerate: this is Labute's definition of a Demushkin
group, and the predicate `IsDemushkin` is characterized here by it. The choice of `φ` is unique up
to a nonzero scalar, and the statements below do not depend on it.

The normal forms of nondegenerate bilinear forms then describe the cup product of a Demushkin group
completely. At an odd prime the cup form is alternating, so `H¹(G, 𝔽_p)` has a symplectic basis, in
which the matrix of the form is the standard block matrix `J`, and the rank of `G` is even. At
`p = 2` the form is symmetric, and there are two cases: if it is alternating there is again a
symplectic basis and the rank is even; if it is not, `H¹(G, 𝔽₂)` has an orthonormal basis, in which
the matrix of the form is the identity, and the rank may be odd. Transporting such a basis to a
change of generators of the free pro-`p` group, which produces the normal forms of the Demushkin
relator, is not treated in this file.

## Main results

* `TauCeti.IsDemushkin.nondegenerate_cupForm`,
  `TauCeti.IsDemushkin.nondegenerate_cupForm_of_ne_zero`: the cup form of a Demushkin group is
  nondegenerate, for every injective, equivalently nonzero, functional on `H²(G, 𝔽_p)`.
* `TauCeti.IsDemushkin.of_nondegenerate_cupForm`, `TauCeti.isDemushkin_iff_nondegenerate_cupForm`:
  **Labute's definition**: a pro-`p` group with finite-dimensional `H¹(G, 𝔽_p)` is Demushkin exactly
  when its cup form is nondegenerate for an isomorphism `H²(G, 𝔽_p) ≅ 𝔽_p`.
* `TauCeti.IsDemushkin.exists_basis_toMatrix_cupForm_eq_J_of_isAlt`,
  `TauCeti.IsDemushkin.exists_basis_toMatrix_cupForm_eq_J_of_ne_two`: when the cup form is
  alternating, in particular at an odd prime, `H¹(G, 𝔽_p)` has a basis in which its matrix is `J`.
* `TauCeti.IsDemushkin.even_demushkinRank_of_isAlt`: an alternating cup form forces even rank.
* `TauCeti.IsDemushkin.exists_basis_toMatrix_cupForm_eq_one_of_not_isAlt`,
  `TauCeti.IsDemushkin.exists_basis_toMatrix_cupForm_eq_J_or_eq_one`: at `p = 2`, a
  non-alternating cup form has an orthonormal basis, and every Demushkin group at `p = 2` falls
  into exactly one of the two cases.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, p. 106
  and Proposition 3.
* J.-P. Serre, *Galois Cohomology*, Chapter I, §4.5.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.9.9).
-/

public section

namespace TauCeti

open Module

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace IsDemushkin

variable (hG : IsDemushkin p G)
include hG

/-- `H²(G, 𝔽_p)` of a Demushkin group is isomorphic to `𝔽_p`. -/
theorem nonempty_linearEquiv_cohomFp_two : Nonempty (cohomFp p G 2 ≃ₗ[ZMod p] ZMod p) :=
  (Module.nonempty_linearEquiv_of_finrank_eq_one hG.finrank_cohomFp_two).map LinearEquiv.symm

/-- A nonzero linear functional on the one-dimensional `H²(G, 𝔽_p)` of a Demushkin group is
injective. -/
theorem injective_of_ne_zero {φ : cohomFp p G 2 →ₗ[ZMod p] ZMod p} (hφ : φ ≠ 0) :
    Function.Injective φ :=
  have : IsSimpleModule (ZMod p) (cohomFp p G 2) :=
    isSimpleModule_iff_finrank_eq_one.mpr hG.finrank_cohomFp_two
  -- the codomain's module structure is pinned to `Semiring.toModule`: under `Fact p.Prime` the
  -- ring structure of `ZMod p` in the type of `φ` is found through `ZMod.instField`, while that of
  -- `H²(G, 𝔽_p)` comes from `ZMod.commRing`, and instance synthesis does not identify the two
  @LinearMap.injective_of_ne_zero (ZMod p) _ (cohomFp p G 2) _ _ (ZMod p) _ Semiring.toModule
    this φ hφ

/-- **The cup form of a Demushkin group is nondegenerate**, for every injective functional
`φ : H²(G, 𝔽_p) →ₗ 𝔽_p`. -/
theorem nondegenerate_cupForm {φ : cohomFp p G 2 →ₗ[ZMod p] ZMod p}
    (hφ : Function.Injective φ) : φ.cupForm.Nondegenerate :=
  (φ.nondegenerate_cupForm_iff_of_injective hφ).2 hG.cup_separatingLeft

/-- The cup form of a Demushkin group is nondegenerate for every nonzero functional on
`H²(G, 𝔽_p)`. -/
theorem nondegenerate_cupForm_of_ne_zero {φ : cohomFp p G 2 →ₗ[ZMod p] ZMod p} (hφ : φ ≠ 0) :
    φ.cupForm.Nondegenerate :=
  hG.nondegenerate_cupForm (hG.injective_of_ne_zero hφ)

/-- **An alternating cup form has a symplectic basis**: when the cup form of a Demushkin group is
alternating, `H¹(G, 𝔽_p)` has a basis indexed by `Fin m ⊕ Fin m` in which its matrix is the
standard block matrix `J`. -/
theorem exists_basis_toMatrix_cupForm_eq_J_of_isAlt {φ : cohomFp p G 2 →ₗ[ZMod p] ZMod p}
    (hφ : φ ≠ 0) (halt : φ.cupForm.IsAlt) :
    ∃ (m : ℕ) (b : Basis (Fin m ⊕ Fin m) (ZMod p) (cohomFp p G 1)),
      LinearMap.BilinForm.toMatrix b φ.cupForm = Matrix.J (Fin m) (ZMod p) := by
  have := hG.finite_cohomFp_one
  exact halt.exists_basis_toMatrix_eq_J (hG.nondegenerate_cupForm_of_ne_zero hφ)

/-- **At an odd prime the cup form has a symplectic basis**: `H¹(G, 𝔽_p)` has a basis indexed by
`Fin m ⊕ Fin m` in which the matrix of the cup form is `J`. -/
theorem exists_basis_toMatrix_cupForm_eq_J_of_ne_two (hp : p ≠ 2)
    {φ : cohomFp p G 2 →ₗ[ZMod p] ZMod p} (hφ : φ ≠ 0) :
    ∃ (m : ℕ) (b : Basis (Fin m ⊕ Fin m) (ZMod p) (cohomFp p G 1)),
      LinearMap.BilinForm.toMatrix b φ.cupForm = Matrix.J (Fin m) (ZMod p) :=
  hG.exists_basis_toMatrix_cupForm_eq_J_of_isAlt hφ (φ.isAlt_cupForm_of_ne_two hp)

section Rank

variable [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **An alternating cup form forces even rank.** -/
theorem even_demushkinRank_of_isAlt {φ : cohomFp p G 2 →ₗ[ZMod p] ZMod p}
    (hφ : φ ≠ 0) (halt : φ.cupForm.IsAlt) : Even (demushkinRank hG) := by
  have := hG.finite_cohomFp_one
  rw [← hG.finrank_cohomFp_one]
  exact halt.even_finrank (hG.nondegenerate_cupForm_of_ne_zero hφ)

end Rank

end IsDemushkin

/-- **Labute's definition of a Demushkin group**: a pro-`p` group `G` with finite-dimensional
`H¹(G, 𝔽_p)`, an isomorphism `e : H²(G, 𝔽_p) ≅ 𝔽_p` and nondegenerate cup form `(a, b) ↦ e (a ⌣ b)`
is Demushkin. The right-separating clause of `IsDemushkin` follows from the left one by graded
commutativity. -/
theorem IsDemushkin.of_nondegenerate_cupForm (hP : IsProP p G)
    (hfin : Module.Finite (ZMod p) (cohomFp p G 1)) (e : cohomFp p G 2 ≃ₗ[ZMod p] ZMod p)
    (hnd : e.toLinearMap.cupForm.Nondegenerate) : IsDemushkin p G where
  isProP := hP
  finite_cohomFp_one := hfin
  finrank_cohomFp_two := by rw [e.finrank_eq, Module.finrank_self]
  cup_separatingLeft := (e.toLinearMap.nondegenerate_cupForm_iff_of_injective e.injective).1 hnd
  cup_separatingRight b hb := by
    obtain ⟨a, ha⟩ := (e.toLinearMap.nondegenerate_cupForm_iff_of_injective e.injective).1 hnd b hb
    exact ⟨a, fun h => ha ((cupFp_eq_zero_comm p G a b).1 h)⟩

/-- **The Demushkin predicate is Labute's definition**: `G` is Demushkin exactly when it is pro-`p`
with finite-dimensional `H¹(G, 𝔽_p)` and its cup form is nondegenerate for some isomorphism
`H²(G, 𝔽_p) ≅ 𝔽_p`; the choice of isomorphism is immaterial by
`LinearMap.nondegenerate_cupForm_iff_of_injective`. -/
theorem isDemushkin_iff_nondegenerate_cupForm :
    IsDemushkin p G ↔ IsProP p G ∧ Module.Finite (ZMod p) (cohomFp p G 1) ∧
      ∃ e : cohomFp p G 2 ≃ₗ[ZMod p] ZMod p, e.toLinearMap.cupForm.Nondegenerate := by
  refine ⟨fun hG => ⟨hG.isProP, hG.finite_cohomFp_one, ?_⟩,
    fun ⟨hP, hfin, e, hnd⟩ => IsDemushkin.of_nondegenerate_cupForm hP hfin e hnd⟩
  obtain ⟨e⟩ := hG.nonempty_linearEquiv_cohomFp_two
  exact ⟨e, hG.nondegenerate_cupForm e.injective⟩

/-! ### The dyadic case

At `p = 2` the cup form is symmetric, and a symmetric nondegenerate form over `𝔽₂` is either
alternating, with a symplectic basis, or has an orthonormal basis. -/

namespace IsDemushkin

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (hG : IsDemushkin 2 G)
include hG

/-- **A non-alternating cup form at `p = 2` has an orthonormal basis**: `H¹(G, 𝔽₂)` has a basis in
which the matrix of the cup form is the identity. -/
theorem exists_basis_toMatrix_cupForm_eq_one_of_not_isAlt {φ : cohomFp 2 G 2 →ₗ[ZMod 2] ZMod 2}
    (hφ : φ ≠ 0) (h : ¬ φ.cupForm.IsAlt) :
    ∃ b : Basis (Fin (finrank (ZMod 2) (cohomFp 2 G 1))) (ZMod 2) (cohomFp 2 G 1),
      LinearMap.BilinForm.toMatrix b φ.cupForm = 1 := by
  have := hG.finite_cohomFp_one
  exact φ.isSymm_cupForm_two.exists_basis_toMatrix_eq_one (fun a => isSquare_of_charTwo' a)
    (hG.nondegenerate_cupForm_of_ne_zero hφ) fun h' => (h h').elim

/-- **The two shapes of the cup form at `p = 2`**: the cup form of a Demushkin group at `p = 2` is
either alternating, with a symplectic basis in which its matrix is `J`, or not alternating, with an
orthonormal basis in which its matrix is the identity. -/
theorem exists_basis_toMatrix_cupForm_eq_J_or_eq_one {φ : cohomFp 2 G 2 →ₗ[ZMod 2] ZMod 2}
    (hφ : φ ≠ 0) :
    (φ.cupForm.IsAlt ∧ ∃ (m : ℕ) (b : Basis (Fin m ⊕ Fin m) (ZMod 2) (cohomFp 2 G 1)),
        LinearMap.BilinForm.toMatrix b φ.cupForm = Matrix.J (Fin m) (ZMod 2)) ∨
      (¬ φ.cupForm.IsAlt ∧
        ∃ b : Basis (Fin (finrank (ZMod 2) (cohomFp 2 G 1))) (ZMod 2) (cohomFp 2 G 1),
          LinearMap.BilinForm.toMatrix b φ.cupForm = 1) := by
  have := hG.finite_cohomFp_one
  exact LinearMap.BilinForm.Nondegenerate.exists_basis_toMatrix_eq_J_or_toMatrix_eq_one
    (fun a => isSquare_of_charTwo' a) (hG.nondegenerate_cupForm_of_ne_zero hφ)
    (Or.inr φ.isSymm_cupForm_two)

end IsDemushkin

end TauCeti
