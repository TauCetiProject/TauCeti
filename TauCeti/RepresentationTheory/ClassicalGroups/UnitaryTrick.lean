/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.PolynomialFunctions.Unitary
public import TauCeti.RepresentationTheory.ClassicalGroups.Rational
public import TauCeti.RepresentationTheory.Compact.Semisimple
public import TauCeti.Topology.Algebra.UnitaryGroup

/-!
# Weyl's unitarian trick for the rational representations of `GL n ℂ`

A rational representation `ρ` of `GL n ℂ` restricts, along the inclusion
`Unitary.toUnits : U(n) →* GL n ℂ` of the unitary group, to a representation of the compact group
`U(n)`. **Weyl's unitarian trick** is that nothing is lost in this restriction: a subspace is
`GL n ℂ`-invariant exactly when it is `U(n)`-invariant, and a linear map between two rational
representations intertwines the `GL n ℂ`-actions exactly when it intertwines the `U(n)`-actions.
Consequently a rational representation is irreducible exactly when its restriction to `U(n)` is,
and, since every finite-dimensional continuous representation of a compact group is completely
reducible, every rational representation of `GL n ℂ` is completely reducible.

The bridge between the two groups is that `U(n)` is Zariski dense in `GL n ℂ`
(`TauCeti.Matrix.GeneralLinearGroup.eq_of_mem_rationalFunctions_of_forall_unitary`), together with
the fact that every matrix coefficient `g ↦ f (ρ g w)` of a rational representation is a rational
function on `GL n ℂ` (`TauCeti.IsRationalRep.dual_apply_mem_rationalFunctions`). If `p` is
`U(n)`-invariant, `w ∈ p`, and `f` is a linear functional vanishing on `p`, the rational function
`g ↦ f (ρ g w)` vanishes on `U(n)`, hence everywhere, so `ρ g w ∈ p` for every `g`.

These are the inputs that let the compact-group theory of `U(n)` (Haar averaging, Schur
orthogonality, the Weyl integration formula) be applied to the rational representations of
`GL n ℂ`. Complete reducibility in particular means that a rational representation is a direct
sum of irreducible ones, so that it is described by the multiplicities of its irreducible
constituents rather than by a composition series alone.

## Main results

* `TauCeti.IsRationalRep.dual_apply_mem_rationalFunctions`: the matrix coefficients of a rational
  representation are rational functions.
* `TauCeti.IsRationalRep.apply_mem_of_forall_unitary`: a subspace invariant under the unitary
  group is invariant under `GL n ℂ`.
* `TauCeti.IsRationalRep.subrepresentationOrderIso`: the subrepresentations of `ρ` are those of
  its restriction to `U(n)`.
* `TauCeti.IsRationalRep.isIrreducible_comp_toUnits_iff`: `ρ` is irreducible exactly when its
  restriction to `U(n)` is.
* `TauCeti.IsRationalRep.isIntertwiningMap_of_comp_toUnits` and
  `TauCeti.IsRationalRep.intertwiningMapEquiv`: the intertwining maps between two rational
  representations are those between their restrictions to `U(n)`.
* `TauCeti.IsRationalRep.continuous_dual_apply_toUnits`: the restriction of a rational
  representation to `U(n)` has continuous matrix coefficients.
* `TauCeti.IsRationalRep.isSemisimpleRepresentation`: **every rational representation of
  `GL n ℂ` is completely reducible.**

## References

* H. Weyl, *The Classical Groups*, Princeton University Press (1939), Chapter VIII, §11.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants* (2009), Section 2.4.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 9.3.
-/

public section

open TauCeti.Matrix.GeneralLinearGroup

namespace TauCeti

namespace IsRationalRep

variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GL (Fin n) ℂ) W}

/-- **The matrix coefficients of a rational representation are rational functions.** For a linear
functional `f` and a vector `w`, the function `g ↦ f (ρ g w)` is a polynomial in the entries of
`g` divided by a power of `det g`. -/
theorem dual_apply_mem_rationalFunctions (h : IsRationalRep ρ) (f : Module.Dual ℂ W) (w : W) :
    (fun g => f (ρ g w)) ∈ rationalFunctions ℂ n := by
  have := h.finite
  let b := Module.finBasis ℂ W
  have hb := (isRationalRep_iff_forall_mem_rationalFunctions b).mp h
  have heq : (fun g => f (ρ g w)) = ∑ i, ∑ j, (b.repr w j * f (b i)) •
      fun g => LinearMap.toMatrix b b (ρ g) i j := by
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, LinearMap.toMatrix_apply]
    conv_lhs => rw [← b.sum_repr w]
    simp only [map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [← b.sum_repr (ρ g (b j))]
    simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [heq]
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ =>
    Subalgebra.smul_mem _ (hb i j) _

/-- **A subspace invariant under the unitary group is invariant under `GL n ℂ`.** If `ρ` is
rational and `p` is preserved by every unitary matrix, then it is preserved by every invertible
matrix: for `w ∈ p` and a linear functional `f` vanishing on `p`, the rational function
`g ↦ f (ρ g w)` vanishes on the unitary group, hence everywhere. -/
theorem apply_mem_of_forall_unitary (h : IsRationalRep ρ) {p : Submodule ℂ W}
    (hp : ∀ u : Matrix.unitaryGroup (Fin n) ℂ, ∀ v ∈ p, ρ (Unitary.toUnits u) v ∈ p)
    (g : GL (Fin n) ℂ) {v : W} (hv : v ∈ p) : ρ g v ∈ p := by
  by_contra hgv
  obtain ⟨f, hf, hpf⟩ := p.exists_le_ker_of_notMem hgv
  refine hf (congrFun (eq_of_mem_rationalFunctions_of_forall_unitary
    (h.dual_apply_mem_rationalFunctions f v) (zero_mem _) fun u => ?_) g)
  exact hpf (hp u v hv)

/-- **The subrepresentations of a rational representation are those of its restriction to the
unitary group.** Restriction along `Unitary.toUnits` keeps the underlying submodule, and every
subspace invariant under the unitary group is already invariant under `GL n ℂ`
(`TauCeti.IsRationalRep.apply_mem_of_forall_unitary`). -/
def subrepresentationOrderIso (h : IsRationalRep ρ) :
    Subrepresentation (ρ.comp (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℂ →* GL (Fin n) ℂ))
      ≃o Subrepresentation ρ where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule g _ hv :=
        h.apply_mem_of_forall_unitary (fun u _ hw => S.apply_mem_toSubmodule u hw) g hv }
  invFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule u _ hv := S.apply_mem_toSubmodule (Unitary.toUnits u) hv }
  left_inv S := by ext; rfl
  right_inv S := by ext; rfl
  map_rel_iff' := by rfl

/-- The correspondence `TauCeti.IsRationalRep.subrepresentationOrderIso` keeps the underlying
submodule. -/
@[simp]
theorem subrepresentationOrderIso_apply_toSubmodule (h : IsRationalRep ρ)
    (S : Subrepresentation
      (ρ.comp (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℂ →* GL (Fin n) ℂ))) :
    (h.subrepresentationOrderIso S).toSubmodule = S.toSubmodule :=
  (rfl)

/-- The inverse correspondence `TauCeti.IsRationalRep.subrepresentationOrderIso` keeps the
underlying submodule. -/
@[simp]
theorem subrepresentationOrderIso_symm_apply_toSubmodule (h : IsRationalRep ρ)
    (S : Subrepresentation ρ) :
    (h.subrepresentationOrderIso.symm S).toSubmodule = S.toSubmodule :=
  (rfl)

/-- **A rational representation is irreducible exactly when its restriction to the unitary group
is.** -/
theorem isIrreducible_comp_toUnits_iff (h : IsRationalRep ρ) :
    Representation.IsIrreducible
        (ρ.comp (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℂ →* GL (Fin n) ℂ)) ↔
      ρ.IsIrreducible :=
  h.subrepresentationOrderIso.isSimpleOrder_iff

section Intertwining

variable {W' : Type*} [AddCommGroup W'] [Module ℂ W'] {σ : Representation ℂ (GL (Fin n) ℂ) W'}

/-- **A linear map between rational representations intertwining the unitary group intertwines
`GL n ℂ`.** For `w` and a linear functional `f`, the two rational functions `g ↦ f (φ (ρ g w))`
and `g ↦ f (σ g (φ w))` agree on the unitary group, hence everywhere. -/
theorem isIntertwiningMap_of_comp_toUnits (hρ : IsRationalRep ρ) (hσ : IsRationalRep σ)
    {φ : W →ₗ[ℂ] W'}
    (hφ : Representation.IsIntertwiningMap
      (ρ.comp (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℂ →* GL (Fin n) ℂ))
      (σ.comp Unitary.toUnits) φ) :
    ρ.IsIntertwiningMap σ φ := by
  refine ⟨fun g w => ?_⟩
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro f
  rw [map_sub, sub_eq_zero]
  refine congrFun (eq_of_mem_rationalFunctions_of_forall_unitary
    (hρ.dual_apply_mem_rationalFunctions (f ∘ₗ φ) w)
    (hσ.dual_apply_mem_rationalFunctions f (φ w)) fun u => ?_) g
  simpa using congrArg f (hφ.isIntertwining u w)

/-- **The intertwining maps between two rational representations are those between their
restrictions to the unitary group**, as a linear equivalence keeping the underlying linear map
(`TauCeti.IsRationalRep.isIntertwiningMap_of_comp_toUnits`). -/
noncomputable def intertwiningMapEquiv (hρ : IsRationalRep ρ) (hσ : IsRationalRep σ) :
    Representation.IntertwiningMap
        (ρ.comp (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℂ →* GL (Fin n) ℂ))
        (σ.comp Unitary.toUnits) ≃ₗ[ℂ] Representation.IntertwiningMap ρ σ where
  toFun φ := φ.toLinearMap.intertwiningMap_of_isIntertwiningMap ρ σ
    (hρ.isIntertwiningMap_of_comp_toUnits hσ
      ⟨fun u w => by simpa using Representation.IntertwiningMap.isIntertwining _ _ φ u w⟩
      ).isIntertwining
  invFun φ := φ.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ fun u w => by
    simpa using Representation.IntertwiningMap.isIntertwining _ _ φ (Unitary.toUnits u) w
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The equivalence `TauCeti.IsRationalRep.intertwiningMapEquiv` keeps the underlying function. -/
@[simp]
theorem coe_intertwiningMapEquiv_apply (hρ : IsRationalRep ρ) (hσ : IsRationalRep σ)
    (φ : Representation.IntertwiningMap
      (ρ.comp (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℂ →* GL (Fin n) ℂ))
      (σ.comp Unitary.toUnits)) :
    ⇑(hρ.intertwiningMapEquiv hσ φ) = ⇑φ :=
  (rfl)

/-- The inverse of `TauCeti.IsRationalRep.intertwiningMapEquiv` keeps the underlying function. -/
@[simp]
theorem coe_intertwiningMapEquiv_symm_apply (hρ : IsRationalRep ρ) (hσ : IsRationalRep σ)
    (φ : Representation.IntertwiningMap ρ σ) :
    ⇑((hρ.intertwiningMapEquiv hσ).symm φ) = ⇑φ :=
  (rfl)

end Intertwining

/-- **The restriction of a rational representation to the unitary group is continuous**: its
matrix coefficients `u ↦ f (ρ u w)` are continuous functions on `U(n)`, being polynomials in the
entries of `u` divided by a power of the nonvanishing `det u`. -/
theorem continuous_dual_apply_toUnits (h : IsRationalRep ρ) (f : Module.Dual ℂ W) (w : W) :
    Continuous fun u : Matrix.unitaryGroup (Fin n) ℂ => f (ρ (Unitary.toUnits u) w) := by
  obtain ⟨P, m, hP⟩ := mem_rationalFunctions_iff_inv.mp (h.dual_apply_mem_rationalFunctions f w)
  have hU : Continuous fun u : Matrix.unitaryGroup (Fin n) ℂ =>
      (u : Matrix (Fin n) (Fin n) ℂ) := continuous_subtype_val
  simp only [hP, Unitary.val_toUnits_apply]
  refine ((hU.matrix_det.pow m).inv₀ fun u => pow_ne_zero m ?_).mul
    ((MvPolynomial.continuous_eval P).comp (continuous_pi fun ij => hU.matrix_elem ij.1 ij.2))
  simpa using _root_.Matrix.GeneralLinearGroup.det_ne_zero (Unitary.toUnits u)

/-- **Every rational representation of `GL n ℂ` is completely reducible.** Its restriction to the
compact group `U(n)` is continuous, hence completely reducible by Haar averaging
(`Representation.isSemisimpleRepresentation_of_continuous`), and it has the same
subrepresentations (`TauCeti.IsRationalRep.subrepresentationOrderIso`). -/
theorem isSemisimpleRepresentation (h : IsRationalRep ρ) : ρ.IsSemisimpleRepresentation := by
  have := h.finite
  exact h.subrepresentationOrderIso.complementedLattice_iff.mp
    (Representation.isSemisimpleRepresentation_of_continuous _ h.continuous_dual_apply_toUnits)

end IsRationalRep

end TauCeti
