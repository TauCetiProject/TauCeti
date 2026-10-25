/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Analysis.Normed.Operator.Surjective
public import TauCeti.LinearAlgebra.Projectivization.ZeroLocus
public import TauCeti.RingTheory.MvPolynomial.Jacobian
public import TauCeti.Topology.Algebra.MvPolynomial.HomogeneousSubmodule
public import TauCeti.Topology.Algebra.Projectivization

/-!
# Projective zero loci and their incidence variety are closed

Complex projective space `ℙ ℂ (Fin N → ℂ)` with its quotient topology is compact and Hausdorff.
The zero locus `complexProjectiveZeroLocus p` of any family of polynomials is closed in it, hence
compact.

For a family of degrees `d : ι → ℕ`, the coefficient space `∀ i, homogeneousSubmodule (Fin N) ℂ
(d i)` parametrizes all families of homogeneous equations of these degrees, the zero equations
included. The incidence variety `complexProjectiveIncidence N d` is the set of pairs `(c, L)` of
such a family and a point of its zero locus, so that its fibre over `c` is the zero locus of the
equations `c i`. It is closed in the product of the coefficient space with projective space.
Since projective space is compact, the projection of the incidence variety to the coefficient
space is a proper map; in particular it maps closed subsets to closed subsets.

The locus `complexProjectiveBadRankLocus N d` of incidence points where the cone Jacobian of
the equations does not have full rank is closed as well, by lower semicontinuity of the rank.
Its projection is therefore closed, and its complement, the set of coefficients all of whose
zero-locus points have full Jacobian rank, is open. This open set is the parameter space for
families of zero loci cut out by equations of full Jacobian rank everywhere.

## Main definitions

* `TauCeti.complexProjectiveIncidence N d`: the incidence variety of pairs `(c, L)` of a family
  `c` of homogeneous equations of degrees `d` in `N` variables and a point `L` of its zero locus.
* `TauCeti.complexProjectiveBadRankLocus N d`: the points of the incidence variety where the
  cone Jacobian of the equations is not surjective.

## Main results

* `TauCeti.isClosed_complexProjectiveZeroLocus`, `TauCeti.isCompact_complexProjectiveZeroLocus`:
  zero loci are closed and compact.
* `TauCeti.mk_preimage_complexProjectiveIncidence`: the fibre of the incidence variety over `c`
  is the zero locus of `c`.
* `TauCeti.isClosed_complexProjectiveIncidence`: the incidence variety is closed.
* `TauCeti.isProperMap_complexProjectiveIncidence_fst`: its projection to the coefficient space
  is proper.
* `TauCeti.isClosed_complexProjectiveBadRankLocus`: the bad-rank locus is closed.
* `TauCeti.isOpen_setOf_forall_mulVec_surjective_jacobiMatrixAt`: the coefficients whose cone
  Jacobian has full rank at every nonzero common zero form an open set.

## References

* J. Harris, *Algebraic Geometry: A First Course*, Lecture 14, for the projective Jacobian
  criterion and the incidence correspondence of hypersurfaces.
-/

public section

open MvPolynomial Topology
open scoped LinearAlgebra.Projectivization

namespace TauCeti

variable {N : ℕ} {ι : Type*}

/-! ### Zero loci are closed -/

/-- The common zero locus of any family of polynomials is closed in complex projective space. -/
theorem isClosed_complexProjectiveZeroLocus (p : ι → MvPolynomial (Fin N) ℂ) :
    IsClosed (complexProjectiveZeroLocus p) := by
  rw [← Projectivization.isQuotientMap_mk'.isClosed_preimage]
  have h : Projectivization.mk' ℂ ⁻¹' complexProjectiveZeroLocus p =
      ⋂ i, ⋂ c : ℂ, {v : {v : Fin N → ℂ // v ≠ 0} | eval (c • v.1) (p i) = 0} := by
    ext v
    simp only [Set.mem_preimage, Projectivization.mk'_eq_mk,
      complexProjectiveZeroLocus_mk_iff_forall_smul, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [h]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun c ↦ isClosed_eq
    ((continuous_eval (p i)).comp ((continuous_const_smul c).comp continuous_subtype_val))
    continuous_const

/-- The common zero locus of any family of polynomials is compact. -/
theorem isCompact_complexProjectiveZeroLocus (p : ι → MvPolynomial (Fin N) ℂ) :
    IsCompact (complexProjectiveZeroLocus p) :=
  (isClosed_complexProjectiveZeroLocus p).isCompact

/-- The zero locus, with the subspace topology, is a compact space. -/
instance (p : ι → MvPolynomial (Fin N) ℂ) : CompactSpace (complexProjectiveZeroLocus p) :=
  isCompact_iff_compactSpace.mp (isCompact_complexProjectiveZeroLocus p)

/-! ### The incidence variety -/

variable (N) in
/-- The **incidence variety** of homogeneous equations of degrees `d` in `N` variables: the pairs
`(c, L)` of a family `c` in the coefficient space `∀ i, homogeneousSubmodule (Fin N) ℂ (d i)` and a
point `L` of complex projective space at which every equation `c i` vanishes. -/
def complexProjectiveIncidence (d : ι → ℕ) :
    Set ((∀ i, homogeneousSubmodule (Fin N) ℂ (d i)) × ℙ ℂ (Fin N → ℂ)) :=
  {x | x.2 ∈ complexProjectiveZeroLocus fun i ↦ (x.1 i : MvPolynomial (Fin N) ℂ)}

variable {d : ι → ℕ}

/-- Membership in the incidence variety unfolds to membership of the point in the zero locus of
the equations. -/
@[simp]
theorem mem_complexProjectiveIncidence
    {x : (∀ i, homogeneousSubmodule (Fin N) ℂ (d i)) × ℙ ℂ (Fin N → ℂ)} :
    x ∈ complexProjectiveIncidence N d ↔
      x.2 ∈ complexProjectiveZeroLocus fun i ↦ (x.1 i : MvPolynomial (Fin N) ℂ) :=
  Iff.rfl

/-- The fibre of the incidence variety over a family of equations `c` is its zero locus. -/
@[simp]
theorem mk_preimage_complexProjectiveIncidence (c : ∀ i, homogeneousSubmodule (Fin N) ℂ (d i)) :
    Prod.mk c ⁻¹' complexProjectiveIncidence N d =
      complexProjectiveZeroLocus fun i ↦ (c i : MvPolynomial (Fin N) ℂ) :=
  (rfl)

/-- A pair `(c, [v])` lies in the incidence variety exactly when every equation `c i` vanishes at
the representative `v`. -/
theorem mk_mem_complexProjectiveIncidence_iff (c : ∀ i, homogeneousSubmodule (Fin N) ℂ (d i))
    (v : Fin N → ℂ) (hv : v ≠ 0) :
    (c, Projectivization.mk ℂ v hv) ∈ complexProjectiveIncidence N d ↔
      ∀ i, eval v (c i : MvPolynomial (Fin N) ℂ) = 0 :=
  complexProjectiveZeroLocus_mk_iff (fun i ↦ (mem_homogeneousSubmodule _ _).mp (c i).2) v hv

/-- On the product of the coefficient space with the nonzero vectors, the common zeros of the
equations form a closed set. -/
private theorem isClosed_setOf_forall_eval_eq_zero :
    IsClosed {x : (∀ i, homogeneousSubmodule (Fin N) ℂ (d i)) × {v : Fin N → ℂ // v ≠ 0} |
      ∀ i, eval x.2.1 (x.1 i : MvPolynomial (Fin N) ℂ) = 0} := by
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun i ↦ isClosed_eq ?_ continuous_const
  have hi : Continuous fun x : (∀ i, homogeneousSubmodule (Fin N) ℂ (d i)) ×
      {v : Fin N → ℂ // v ≠ 0} ↦ (x.1 i, x.2.1) := by fun_prop
  exact (continuous_eval_homogeneousSubmodule (σ := Fin N) (R := ℂ) (d i)).comp hi

/-- The incidence variety is closed in the product of the coefficient space with projective
space. -/
theorem isClosed_complexProjectiveIncidence (d : ι → ℕ) :
    IsClosed (complexProjectiveIncidence N d) := by
  rw [← (IsOpenQuotientMap.id.prodMap
    Projectivization.isOpenQuotientMap_mk').isQuotientMap.isClosed_preimage]
  convert isClosed_setOf_forall_eval_eq_zero (d := d) using 1
  ext ⟨c, v⟩
  simp only [Set.mem_preimage, Prod.map_apply, id_eq, Projectivization.mk'_eq_mk,
    mk_mem_complexProjectiveIncidence_iff, Set.mem_ofPred_eq]

/-- **The incidence projection is proper.** Projecting the incidence variety to the coefficient
space is a proper map, since projective space is compact. In particular the image of every
closed subset of the incidence variety is closed. -/
theorem isProperMap_complexProjectiveIncidence_fst (d : ι → ℕ) :
    IsProperMap fun x : complexProjectiveIncidence N d ↦ x.1.1 :=
  isProperMap_fst_of_compactSpace.restrict (isClosed_complexProjectiveIncidence d)

/-! ### The bad-rank locus -/

variable (N) in
/-- The **bad-rank locus** of the incidence variety: the pairs `(c, L)` in the incidence variety
at which the cone Jacobian of the equations `c i`, evaluated at a representative of `L`, is not
surjective. By `mk_mem_complexProjectiveBadRankLocus_iff` this does not depend on the chosen
representative. -/
def complexProjectiveBadRankLocus (d : ι → ℕ) :
    Set ((∀ i, homogeneousSubmodule (Fin N) ℂ (d i)) × ℙ ℂ (Fin N → ℂ)) :=
  {x | x ∈ complexProjectiveIncidence N d ∧
    ¬(jacobiMatrixAt (fun i ↦ (x.1 i : MvPolynomial (Fin N) ℂ)) x.2.rep).mulVec.Surjective}

/-- Membership in the bad-rank locus unfolds to membership in the incidence variety and failure
of surjectivity of the cone Jacobian at the chosen representative. -/
theorem mem_complexProjectiveBadRankLocus
    {x : (∀ i, homogeneousSubmodule (Fin N) ℂ (d i)) × ℙ ℂ (Fin N → ℂ)} :
    x ∈ complexProjectiveBadRankLocus N d ↔ x ∈ complexProjectiveIncidence N d ∧
      ¬(jacobiMatrixAt (fun i ↦ (x.1 i : MvPolynomial (Fin N) ℂ)) x.2.rep).mulVec.Surjective :=
  Iff.rfl

/-- The bad-rank locus is contained in the incidence variety. -/
theorem complexProjectiveBadRankLocus_subset (d : ι → ℕ) :
    complexProjectiveBadRankLocus N d ⊆ complexProjectiveIncidence N d :=
  fun _ hx ↦ hx.1

/-- A pair `(c, [v])` lies in the bad-rank locus exactly when every equation `c i` vanishes at
`v` and the cone Jacobian of the equations at `v` is not surjective, for any representative
`v`. -/
theorem mk_mem_complexProjectiveBadRankLocus_iff [Finite ι]
    (c : ∀ i, homogeneousSubmodule (Fin N) ℂ (d i)) (v : Fin N → ℂ) (hv : v ≠ 0) :
    (c, Projectivization.mk ℂ v hv) ∈ complexProjectiveBadRankLocus N d ↔
      (∀ i, eval v (c i : MvPolynomial (Fin N) ℂ) = 0) ∧
        ¬(jacobiMatrixAt (fun i ↦ (c i : MvPolynomial (Fin N) ℂ)) v).mulVec.Surjective := by
  rw [mem_complexProjectiveBadRankLocus, mk_mem_complexProjectiveIncidence_iff,
    mulVec_surjective_jacobiMatrixAt_iff_of_mk_eq_mk
      (fun i ↦ (mem_homogeneousSubmodule _ _).mp (c i).2) (Projectivization.rep_nonzero _) hv
      (Projectivization.mk_rep _)]

/-- The bad-rank locus is closed: the cone Jacobian depends continuously on the coefficients and
the point, and full rank is an open condition. -/
theorem isClosed_complexProjectiveBadRankLocus [Finite ι] (d : ι → ℕ) :
    IsClosed (complexProjectiveBadRankLocus N d) := by
  rw [← (IsOpenQuotientMap.id.prodMap
    Projectivization.isOpenQuotientMap_mk').isQuotientMap.isClosed_preimage]
  have hJ : Continuous fun x : (∀ i, homogeneousSubmodule (Fin N) ℂ (d i)) ×
      {v : Fin N → ℂ // v ≠ 0} ↦ jacobiMatrixAt (fun i ↦ (x.1 i : MvPolynomial (Fin N) ℂ)) x.2.1 :=
    (continuous_jacobiMatrixAt_homogeneousSubmodule d).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  convert isClosed_setOf_forall_eval_eq_zero.inter
    (isOpen_setOf_mulVec_surjective.preimage hJ).isClosed_compl using 1
  ext ⟨c, v⟩
  simp only [Set.mem_preimage, Prod.map_apply, id_eq, Projectivization.mk'_eq_mk,
    mk_mem_complexProjectiveBadRankLocus_iff, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Set.mem_compl_iff]

/-- The projection of the bad-rank locus to the coefficient space is closed. -/
theorem isClosed_image_fst_complexProjectiveBadRankLocus [Finite ι] (d : ι → ℕ) :
    IsClosed (Prod.fst '' complexProjectiveBadRankLocus N d) :=
  isClosedMap_fst_of_compactSpace _ (isClosed_complexProjectiveBadRankLocus d)

/-- **Full rank is an open condition on the equations.** The families `c` of homogeneous
equations of degrees `d` whose cone Jacobian is surjective at every nonzero common zero form an
open subset of the coefficient space. -/
theorem isOpen_setOf_forall_mulVec_surjective_jacobiMatrixAt [Finite ι] (d : ι → ℕ) :
    IsOpen {c : ∀ i, homogeneousSubmodule (Fin N) ℂ (d i) | ∀ v : Fin N → ℂ, v ≠ 0 →
      (∀ i, eval v (c i : MvPolynomial (Fin N) ℂ) = 0) →
        (jacobiMatrixAt (fun i ↦ (c i : MvPolynomial (Fin N) ℂ)) v).mulVec.Surjective} := by
  convert (isClosed_image_fst_complexProjectiveBadRankLocus (N := N) d).isOpen_compl using 1
  ext c
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
  refine ⟨fun h ⟨c', L⟩ hL hc ↦ ?_, fun h v hv hz ↦ not_not.mp fun hS ↦
    h (c, Projectivization.mk ℂ v hv) ((mk_mem_complexProjectiveBadRankLocus_iff c v hv).2
      ⟨hz, hS⟩) rfl⟩
  obtain rfl : c' = c := hc
  rw [← L.mk_rep, mk_mem_complexProjectiveBadRankLocus_iff] at hL
  exact hL.2 (h _ L.rep_nonzero hL.1)

end TauCeti
