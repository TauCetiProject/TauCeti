/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeA.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeE.Basic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.SimplyLaced

/-!
# The root lattice of a simply-laced Dynkin type

For a simply-laced Dynkin type `t` (types `A`, `D`, `E₆`, `E₇`, `E₈`), the Cartan matrix
`t.cartanMatrix` is symmetric and positive definite, so it is the Gram matrix of a positive
definite integral lattice.  This file constructs that lattice uniformly in `t`,

```text
t.rootLattice ht = ℤ^{rank t} ⊆ ℚ^{rank t},   ⟨x, y⟩ = xᵀ (cartanMatrix t) y,
```

so that the standard coordinate vectors are the simple roots in Bourbaki numbering.  It proves the
properties every orthogonal sum of such lattices inherits: the simple roots form a `ℤ`-basis with
Gram matrix `t.cartanMatrix`, the lattice has rank `t.rank`, it is even and positive definite, its
determinant is `det t.cartanMatrix`, and its norm-`2` vectors span the whole carrier.

Uniformity is the point of the construction: an ordered list of ADE components is a list of Dynkin
types, and the orthogonal sum of their root lattices has to be formed without a case split on each
component.  The case split is done once, here, by identifying the uniform lattice with the
family-specific models that carry the discriminant-form computations:

* `(A n).rootLattice _` and the three exceptional lattices are literally the simple-root lattices
  `TauCeti.IntegralLattice.typeARootLattice n`, `typeE₆RootLattice`, `typeE₇RootLattice` and
  `typeE₈RootLattice`;
* for `4 ≤ n`, `(D n).rootLattice _` is isometric to the Conway--Sloane checkerboard lattice
  `TauCeti.IntegralLattice.checkerboardLattice n`, by the isometry sending the `i`-th simple root
  to the `i`-th Bourbaki simple root `TauCeti.IntegralLattice.checkerboardSimpleRoot n hn i`.

The hypothesis is that the *type* is simply laced.  Only the symmetry and positive definiteness of
the Cartan matrix are used, and these also hold for the degenerate names `B 0`, `B 1`, `C 0` and
`C 1`, whose matrices are those of type `A`; those names are not types of root systems, so they
are excluded here (`TauCeti.DynkinType.isSimplyLaced_cartanMatrix_iff`).

## Main declarations

* `TauCeti.DynkinType.rootLattice`: the positive root lattice of a simply-laced Dynkin type.
* `TauCeti.DynkinType.simpleRootBasis`: its simple-root `ℤ`-basis.
* `TauCeti.DynkinType.gramMatrix_simpleRootBasis`: the Gram matrix of that basis is the Cartan
  matrix.
* `TauCeti.DynkinType.finrank_rootLattice`, `isEven_rootLattice`, `isPosDef_rootLattice`,
  `determinant_rootLattice`, `minimum_rootLattice`: rank, evenness, positive definiteness,
  determinant and minimum.
* `TauCeti.DynkinType.span_vectorsOfNorm_two_rootLattice`: the norm-`2` vectors span the carrier.
* `TauCeti.DynkinType.eq_rootLattice`: a lattice with integral coordinates and Cartan Gram matrix
  is the root lattice.
* `TauCeti.DynkinType.rootLattice_A`, `rootLattice_E6`, `rootLattice_E7`, `rootLattice_E8`:
  identification with the family-specific simple-root lattices.
* `TauCeti.DynkinType.rootLatticeIsometryCheckerboard`: the isometry of the type `Dₙ` root lattice
  with the checkerboard lattice.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates I--VII, for the Cartan
  matrices and the simple-root numbering.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §§6--8,
  for the root lattices `Aₙ`, `Dₙ`, `E₆`, `E₇`, `E₈`.
-/

public section

namespace TauCeti.DynkinType

open IntegralLattice _root_.Matrix

variable (t : DynkinType) (ht : t.IsSimplyLaced)

/-- **The positive root lattice of a simply-laced Dynkin type** `t`: the integral lattice on
`Fin t.rank → ℚ` whose Gram matrix in the standard basis is the Cartan matrix `t.cartanMatrix`.
The standard coordinate vectors are the simple roots, in Bourbaki numbering. -/
noncomputable def rootLattice : IntegralLattice (Fin t.rank → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin t.rank)) t.cartanMatrix
    (cartanMatrix_isSymm_of_isSimplyLaced ((isSimplyLaced_cartanMatrix_iff t).mpr (.inl ht)))

/-- The carrier of the root lattice is the `ℤ`-span of the standard coordinate vectors, the simple
roots. -/
theorem rootLattice_carrier :
    (t.rootLattice ht).carrier = Submodule.span ℤ (Set.range fun i : Fin t.rank ↦ Pi.single i 1) :=
  funext (Pi.basisFun_apply ℚ (Fin t.rank)) ▸ ofGramMatrix_carrier _ _ _

/-- A vector belongs to the root lattice exactly when all of its simple-root coordinates are
integers. -/
@[simp]
theorem mem_rootLattice_carrier_iff (x : Fin t.rank → ℚ) :
    x ∈ (t.rootLattice ht).carrier ↔ ∀ i, ∃ z : ℤ, (z : ℚ) = x i :=
  mem_ofGramMatrix_basisFun_carrier_iff _ _ x

/-- The form of the root lattice, expanded in simple-root coordinates. -/
theorem rootLattice_form_apply (x y : Fin t.rank → ℚ) :
    (t.rootLattice ht).form x y = ∑ i, x i * ∑ j, ((t.cartanMatrix i j : ℤ) : ℚ) * y j :=
  form_ofGramMatrix_basisFun_apply _ _ x y

/-- The rational norm of an integer vector of the root lattice is its integral Cartan norm
`vᵀ (cartanMatrix t) v`. -/
theorem norm_rootLattice_intCast (v : Fin t.rank → ℤ) :
    (t.rootLattice ht).norm (fun j ↦ (v j : ℚ)) = (((v ᵥ* t.cartanMatrix) ⬝ᵥ v : ℤ) : ℚ) :=
  norm_ofGramMatrix_basisFun_intCast _ _ v

/-- The simple roots, as a `ℤ`-basis of the root lattice. -/
noncomputable def simpleRootBasis : Module.Basis (Fin t.rank) ℤ (t.rootLattice ht) :=
  ofGramMatrix.basis _ _ _

/-- The `i`-th simple root is the `i`-th standard coordinate vector. -/
@[simp]
theorem coe_simpleRootBasis (i : Fin t.rank) :
    (t.simpleRootBasis ht i : Fin t.rank → ℚ) = Pi.single i 1 := by
  exact (ofGramMatrix.coe_basis _ _ _ i).trans (Pi.basisFun_apply ℚ _ i)

/-- **The Gram matrix of the root lattice in its simple-root basis is the Cartan matrix.** -/
@[simp]
theorem gramMatrix_simpleRootBasis :
    (t.rootLattice ht).gramMatrix (t.simpleRootBasis ht) = t.cartanMatrix :=
  gramMatrix_ofGramMatrix _ _ _

/-- The pairing of two simple roots is the corresponding Cartan integer. -/
@[simp]
theorem rootLattice_form_single_single (i j : Fin t.rank) :
    (t.rootLattice ht).form (Pi.single i 1) (Pi.single j 1) = ((t.cartanMatrix i j : ℤ) : ℚ) := by
  rw [← coe_simpleRootBasis t ht, ← coe_simpleRootBasis t ht, ← intCast_gramMatrix_apply,
    gramMatrix_simpleRootBasis]

/-- **The root lattice of `t` has rank `t.rank`.** -/
@[simp]
theorem finrank_rootLattice : Module.finrank ℤ (t.rootLattice ht) = t.rank := by
  rw [Module.finrank_eq_card_basis (t.simpleRootBasis ht), Fintype.card_fin]

/-- **The root lattice is even**: every diagonal Cartan entry is `2`. -/
theorem isEven_rootLattice : (t.rootLattice ht).IsEven := by
  rw [rootLattice, isEven_ofGramMatrix_iff]
  intro i
  rw [cartanMatrix_apply_same]
  exact even_two

/-- **The root lattice is positive definite**, the Cartan matrix of a simply-laced type being
positive definite. -/
theorem isPosDef_rootLattice : (t.rootLattice ht).IsPosDef := by
  rw [rootLattice, isPosDef_ofGramMatrix_iff]
  exact ht.posDef_map_intCast_cartanMatrix

/-- The root lattice is nondegenerate, being positive definite. -/
instance : (t.rootLattice ht).IsNondegenerate :=
  ⟨((t.rootLattice ht).isPosDef_iff_isPosSemidef_and_nondegenerate.mp
    (t.isPosDef_rootLattice ht)).2⟩

/-- **The determinant of the root lattice is the determinant of the Cartan matrix.** -/
@[simp]
theorem determinant_rootLattice : (t.rootLattice ht).determinant = t.cartanMatrix.det := by
  rw [rootLattice, determinant_ofGramMatrix]

/-- Every simple root has norm `2`. -/
@[simp]
theorem rootLattice_norm_single (i : Fin t.rank) : (t.rootLattice ht).norm (Pi.single i 1) = 2 := by
  rw [norm_apply, rootLattice_form_single_single, cartanMatrix_apply_same]
  norm_num

/-- **The norm-`2` vectors of the root lattice span its carrier**: the simple roots have norm `2`
and form a `ℤ`-basis. -/
theorem span_vectorsOfNorm_two_rootLattice :
    Submodule.span ℤ
        ((fun x : t.rootLattice ht ↦ (x : Fin t.rank → ℚ)) '' (t.rootLattice ht).vectorsOfNorm 2) =
      (t.rootLattice ht).carrier := by
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · refine (t.rootLattice_carrier ht).le.trans (Submodule.span_le.mpr ?_)
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨t.simpleRootBasis ht i,
      mem_vectorsOfNorm.mpr (by rw [coe_simpleRootBasis, rootLattice_norm_single]),
      coe_simpleRootBasis t ht i⟩

/-- **A root lattice of positive rank has minimum `2`**: it is even and a simple root has norm
`2`. -/
@[simp]
theorem minimum_rootLattice (h : t.rank ≠ 0) : (t.rootLattice ht).minimum = 2 :=
  (t.isPosDef_rootLattice ht).minimum_eq_two (t.isEven_rootLattice ht)
    (x := t.simpleRootBasis ht ⟨0, Nat.pos_of_ne_zero h⟩) <| by
      rw [integralNorm_apply, ← gramMatrix_apply, gramMatrix_simpleRootBasis,
        cartanMatrix_apply_same]

/-! ## Identification with the family-specific models -/

/-- **Characterization of the root lattice**: an integral lattice on `Fin t.rank → ℚ` whose
carrier is the standard integral lattice `ℤ^{rank t}`, and whose form pairs the standard basis
vectors by the Cartan integers, is the root lattice of `t`. -/
theorem eq_rootLattice {L : IntegralLattice (Fin t.rank → ℚ)}
    (hcarrier : ∀ x, x ∈ L.carrier ↔ ∀ i, ∃ z : ℤ, (z : ℚ) = x i)
    (hform : ∀ i j, L.form (Pi.single i 1) (Pi.single j 1) = ((t.cartanMatrix i j : ℤ) : ℚ)) :
    L = t.rootLattice ht := by
  refine IntegralLattice.ext (Submodule.ext fun x ↦
    (hcarrier x).trans (t.mem_rootLattice_carrier_iff ht x).symm) ?_
  refine LinearMap.BilinForm.ext_basis (Pi.basisFun ℚ (Fin t.rank)) fun i j ↦ ?_
  rw [Pi.basisFun_apply, Pi.basisFun_apply, hform, rootLattice_form_single_single]

/-- The root lattice of type `Aₙ` is the simple-root lattice `typeARootLattice n`. -/
theorem rootLattice_A (n : ℕ) (ht : (A n).IsSimplyLaced) :
    (A n).rootLattice ht = typeARootLattice n := by
  refine ((A n).eq_rootLattice ht (L := typeARootLattice n)
    (mem_typeARootLattice_carrier_iff n) fun i j ↦ ?_).symm
  have hs (k : Fin n) : typeASimpleRoot n k = Pi.single k 1 := by ext; simp [Pi.single_apply]
  have h := form_typeASimpleRoot_typeASimpleRoot n i j
  rw [hs i, hs j] at h
  exact h.trans (congrArg _ (congr_fun₂ (cartanMatrix_A n) i j).symm)

/-- The root lattice of type `E₆` is the simple-root lattice `typeE₆RootLattice`. -/
theorem rootLattice_E6 (ht : E6.IsSimplyLaced) : E6.rootLattice ht = typeE₆RootLattice := by
  refine (E6.eq_rootLattice ht (L := typeE₆RootLattice)
    mem_typeE₆RootLattice_carrier_iff fun i j ↦ ?_).symm
  have hs (k : Fin 6) : typeE₆SimpleRoot k = Pi.single k 1 := by ext; simp [Pi.single_apply]
  have h := form_typeE₆SimpleRoot_typeE₆SimpleRoot i j
  rw [hs i, hs j] at h
  exact h.trans (congrArg _ (congr_fun₂ cartanMatrix_E6 i j).symm)

/-- The root lattice of type `E₇` is the simple-root lattice `typeE₇RootLattice`. -/
theorem rootLattice_E7 (ht : E7.IsSimplyLaced) : E7.rootLattice ht = typeE₇RootLattice := by
  refine (E7.eq_rootLattice ht (L := typeE₇RootLattice)
    mem_typeE₇RootLattice_carrier_iff fun i j ↦ ?_).symm
  have hs (k : Fin 7) : typeE₇SimpleRoot k = Pi.single k 1 := by ext; simp [Pi.single_apply]
  have h := form_typeE₇SimpleRoot_typeE₇SimpleRoot i j
  rw [hs i, hs j] at h
  exact h.trans (congrArg _ (congr_fun₂ cartanMatrix_E7 i j).symm)

/-- The root lattice of type `E₈` is the simple-root lattice `typeE₈RootLattice`. -/
theorem rootLattice_E8 (ht : E8.IsSimplyLaced) : E8.rootLattice ht = typeE₈RootLattice := by
  refine (E8.eq_rootLattice ht (L := typeE₈RootLattice)
    mem_typeE₈RootLattice_carrier_iff fun i j ↦ ?_).symm
  have hs (k : Fin 8) : typeE₈SimpleRoot k = Pi.single k 1 := by ext; simp [Pi.single_apply]
  have h := form_typeE₈SimpleRoot_typeE₈SimpleRoot i j
  rw [hs i, hs j] at h
  exact h.trans (congrArg _ (congr_fun₂ cartanMatrix_E8 i j).symm)

/-- **The root lattice of type `Dₙ` is the checkerboard lattice.**  For `4 ≤ n`, the isometry
sends the `i`-th simple root to the `i`-th Bourbaki simple root of the Conway--Sloane coordinate
model `{x ∈ ℤⁿ | ∑ xᵢ even}`; both bases have Gram matrix `CartanMatrix.D n`. -/
noncomputable def rootLatticeIsometryCheckerboard (n : ℕ) (hn : 4 ≤ n)
    (ht : (D n).IsSimplyLaced) :
    IntegralLattice.Isometry ((D n).rootLattice ht) (checkerboardLattice n) :=
  Isometry.ofGramMatrixEq ((D n).simpleRootBasis ht) (checkerboardSimpleRootBasis n hn) <|
    ((D n).gramMatrix_simpleRootBasis ht).trans
      ((cartanMatrix_D n).trans (gramMatrix_checkerboardSimpleRootBasis hn).symm)

/-- The isometry `rootLatticeIsometryCheckerboard` sends the `i`-th simple root to the `i`-th
Bourbaki simple root of the checkerboard lattice. -/
-- Not a `simp` lemma: `rank_D` rewrites the index type `Fin (D n).rank` of `Pi.single` on the
-- left-hand side, so the statement is not in simp-normal form.
theorem rootLatticeIsometryCheckerboard_single (n : ℕ) (hn : 4 ≤ n)
    (ht : (D n).IsSimplyLaced) (i : Fin n) :
    rootLatticeIsometryCheckerboard n hn ht (Pi.single i 1) = checkerboardSimpleRoot n hn i :=
  (congrArg _ ((D n).coe_simpleRootBasis ht i).symm).trans <|
    (Isometry.ofGramMatrixEq_apply_basis _ _ _ i).trans (coe_checkerboardSimpleRootBasis_apply hn i)

end TauCeti.DynkinType
