/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RadicalQuotient
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.Dynkin
public import TauCeti.LinearAlgebra.IntegralLattice.Scaling
public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Deletion
import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.PositiveSemidefinite

/-!
# The affine root lattice and its radical quotient

For an affine simply-laced Dynkin diagram `t` (the affine diagrams `Aₙ`, `Dₙ`, `E₆`, `E₇`,
`E₈` of `TauCeti.AffineDynkinType`), the generalized Cartan matrix `t.cartanMatrix` is
symmetric, so it is the Gram matrix of an integral lattice

```text
t.rootLattice = ℤ^{nodes t} ⊆ ℚ^{nodes t},   ⟨x, y⟩ = xᵀ (cartanMatrix t) y,
```

the affine root lattice, whose standard coordinate vectors are the simple roots. Unlike a finite
root lattice it is degenerate: its form is positive semidefinite, and its radical is the line
spanned by the marks `δ` of the diagram, the null root. The marks equal `1` at the affine node, so
`δ` is primitive and the vectors of the radical lying in the lattice are exactly the integer
multiples of `δ`. Deleting the affine node leaves the finite diagram `t.finiteType`, and the
radical quotient of the affine root lattice is the finite root lattice of that type:

```text
t.rootLattice ⧸ radical ≅ t.finiteType.rootLattice.
```

The isometry sends the class of `v` to the vector `i ↦ v (b i) - v (a) δ (b i)`, where `a` is the
affine node and `b` the Bourbaki relabelling `t.bourbakiNode` of the remaining nodes, that is, it
first moves `v` to the representative of its class vanishing at the affine node. Its inverse
extends a vector of the finite root lattice by zero at the affine node.

Negating the form gives the same statements for the negative semidefinite lattice
`-t.rootLattice`, whose radical quotient is the negative definite lattice
`-t.finiteType.rootLattice`. This is the form in which the lattice arises in geometry: the
intersection matrix of the components of a reducible fibre of a genus-one fibration on a surface
is `-cartanMatrix t` for the affine type `t` of the fibre, its radical is spanned by the
multiplicity vector of the fibre, and the quotient by this radical is the negative definite root
lattice of the finite type `t.finiteType`. On a K3 surface these quotients make up the root
lattice of the fibration, whose determinant enters the comparison of the Mordell–Weil group with
the Picard lattice.

## Main definitions and results

* `TauCeti.AffineDynkinType.rootLattice`: the affine root lattice, with Gram matrix the
  generalized Cartan matrix.
* `TauCeti.AffineDynkinType.radical_rootLattice`: its radical is the line spanned by the marks.
* `TauCeti.AffineDynkinType.mem_rootLattice_carrier_and_mem_radical_iff`: the lattice vectors of
  the radical are the integer multiples of the marks.
* `TauCeti.AffineDynkinType.signature_rootLattice` and
  `TauCeti.AffineDynkinType.isPosSemidef_rootLattice`: the lattice is positive semidefinite of
  signature `(rank, 1, 0)`, with `rank` the rank of the finite type.
* `TauCeti.AffineDynkinType.radicalQuotientIsometry`: the radical quotient is isometric to the
  finite root lattice.
* `TauCeti.AffineDynkinType.determinant_radicalQuotient_rootLattice`: the determinant of the
  radical quotient is the determinant of the finite Cartan matrix.
* `TauCeti.AffineDynkinType.negRadicalQuotientIsometry`,
  `TauCeti.AffineDynkinType.isNegDef_radicalQuotient_neg_rootLattice` and
  `TauCeti.AffineDynkinType.discriminant_radicalQuotient_neg_rootLattice`: the negated lattice
  has the negative definite finite root lattice as radical quotient, with discriminant the
  absolute value of the determinant of the finite Cartan matrix.

## References

* V. Kac, *Infinite dimensional Lie algebras*, 3rd ed., Chapter 6, for the affine root lattice,
  the null root `δ` and the finite root lattice it extends.
* W. Barth, K. Hulek, C. Peters and A. Van de Ven, *Compact complex surfaces*, 2nd ed.,
  Chapter V, §7, and F. Cossec, I. Dolgachev and C. Liedtke, *Enriques surfaces I*, Theorem 4.1.4,
  for the fibre components of a genus-one fibration and their root lattices.
-/

public section

namespace TauCeti

open IntegralLattice _root_.Matrix

namespace AffineDynkinType

variable (t : AffineDynkinType)

/-- **The affine root lattice** of an affine simply-laced Dynkin diagram `t`: the integral lattice
on `Fin t.nodes → ℚ` whose Gram matrix in the standard basis is the generalized Cartan matrix
`t.cartanMatrix`. The standard coordinate vectors are the simple roots, including the affine one.
For a valid diagram the lattice is degenerate: its radical is spanned by the marks
(`TauCeti.AffineDynkinType.radical_rootLattice`). -/
noncomputable def rootLattice : IntegralLattice (Fin t.nodes → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin t.nodes)) t.cartanMatrix t.isSymm_cartanMatrix

variable {t}

/-- A vector belongs to the affine root lattice exactly when all of its simple-root coordinates are
integers. -/
@[simp]
theorem mem_rootLattice_carrier_iff (x : Fin t.nodes → ℚ) :
    x ∈ t.rootLattice.carrier ↔ ∀ i, ∃ z : ℤ, (z : ℚ) = x i :=
  mem_ofGramMatrix_basisFun_carrier_iff _ _ x

/-- The form of the affine root lattice, expanded in simple-root coordinates. -/
theorem rootLattice_form_apply (x y : Fin t.nodes → ℚ) :
    t.rootLattice.form x y = ∑ i, x i * ∑ j, ((t.cartanMatrix i j : ℤ) : ℚ) * y j :=
  form_ofGramMatrix_basisFun_apply _ _ x y

/-- The form pairs the `i`-th and `j`-th simple roots to the `(i, j)` entry of the generalized
Cartan matrix. -/
@[simp]
theorem rootLattice_form_single_single (i j : Fin t.nodes) :
    t.rootLattice.form (Pi.single i 1) (Pi.single j 1) = t.cartanMatrix i j := by
  have h := form_ofGramMatrix_basisFun_basisFun t.cartanMatrix t.isSymm_cartanMatrix i j
  rwa [Pi.basisFun_apply, Pi.basisFun_apply] at h

/-- The affine root lattice is even: every simple root has norm `2`. -/
theorem isEven_rootLattice : t.rootLattice.IsEven :=
  (isEven_ofGramMatrix_iff _ _ _).2 fun i ↦ by rw [cartanMatrix_apply_same]; exact even_two

/-! ### The radical -/

/-- A vector lies in the radical of the affine root lattice exactly when the generalized Cartan
matrix kills it. -/
theorem mem_radical_rootLattice_iff (x : Fin t.nodes → ℚ) :
    x ∈ t.rootLattice.radical ↔ t.cartanMatrix.map ((↑) : ℤ → ℚ) *ᵥ x = 0 := by
  have hform (i : Fin t.nodes) :
      t.rootLattice.form x (Pi.basisFun ℚ _ i) = (t.cartanMatrix.map ((↑) : ℤ → ℚ) *ᵥ x) i := by
    rw [rootLattice, form_ofGramMatrix_basisFun_right]
    simp [mulVec, dotProduct]
  rw [mem_radical_iff]
  refine ⟨fun h ↦ funext fun i ↦ by rw [← hform, h, Pi.zero_apply], fun h y ↦ ?_⟩
  have hx : t.rootLattice.form x = 0 :=
    (Pi.basisFun ℚ (Fin t.nodes)).ext fun i ↦ by rw [hform, h, Pi.zero_apply, LinearMap.zero_apply]
  rw [hx, LinearMap.zero_apply]

/-- A rational vector killed by the generalized Cartan matrix of a valid diagram is its value at
the affine node times the marks. This is the rational form of
`TauCeti.AffineDynkinType.ker_mulVecLin_realCartanMatrix`, normalized by
`TauCeti.AffineDynkinType.marks_affineNode`. -/
private lemma smul_marks_eq_of_mulVec_eq_zero (ht : t.Valid) {x : Fin t.nodes → ℚ}
    (hx : t.cartanMatrix.map ((↑) : ℤ → ℚ) *ᵥ x = 0) :
    x t.affineNode • (fun i ↦ (t.marks i : ℚ)) = x := by
  have hr : (fun i ↦ (x i : ℝ)) ∈ LinearMap.ker (mulVecLin t.realCartanMatrix) := by
    rw [LinearMap.mem_ker, mulVecLin_apply, realCartanMatrix_eq_map]
    funext i
    have hi := congrFun hx i
    simp only [mulVec, dotProduct, map_apply, Pi.zero_apply] at hi ⊢
    exact_mod_cast hi
  rw [ker_mulVecLin_realCartanMatrix ht, Submodule.mem_span_singleton] at hr
  obtain ⟨c, hc⟩ := hr
  have ha : c = x t.affineNode := by simpa using congrFun hc t.affineNode
  funext i
  have hi := congrFun hc i
  simp only [Pi.smul_apply, smul_eq_mul, ha] at hi ⊢
  exact_mod_cast hi

/-- The rational marks are killed by the generalized Cartan matrix. -/
private lemma mulVec_marks_eq_zero (ht : t.Valid) :
    t.cartanMatrix.map ((↑) : ℤ → ℚ) *ᵥ (fun i ↦ (t.marks i : ℚ)) = 0 := by
  funext i
  have hi := congrFun (cartanMatrix_mulVec_marks_eq_zero ht) i
  simp only [mulVec, dotProduct, map_apply, Pi.zero_apply] at hi ⊢
  exact_mod_cast hi

/-- **The radical of the affine root lattice is the line spanned by the marks**, the null root
`δ`. -/
theorem radical_rootLattice (ht : t.Valid) :
    t.rootLattice.radical = ℚ ∙ (fun i ↦ (t.marks i : ℚ)) := by
  ext x
  rw [mem_radical_rootLattice_iff, Submodule.mem_span_singleton]
  refine ⟨fun h ↦ ⟨x t.affineNode, smul_marks_eq_of_mulVec_eq_zero ht h⟩, ?_⟩
  rintro ⟨c, rfl⟩
  rw [mulVec_smul, mulVec_marks_eq_zero ht, smul_zero]

/-- **The marks generate the radical integrally**: the vectors of the affine root lattice lying in
its radical are exactly the integer multiples of the marks. Since the mark at the affine node is
`1`, a rational multiple of the marks is a lattice vector only when the multiple is an integer. -/
theorem mem_rootLattice_carrier_and_mem_radical_iff (ht : t.Valid) (x : Fin t.nodes → ℚ) :
    x ∈ t.rootLattice.carrier ∧ x ∈ t.rootLattice.radical ↔
      ∃ n : ℤ, (n : ℚ) • (fun i ↦ (t.marks i : ℚ)) = x := by
  rw [radical_rootLattice ht, mem_rootLattice_carrier_iff, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨hx, c, rfl⟩
    obtain ⟨n, hn⟩ := hx t.affineNode
    refine ⟨n, ?_⟩
    rw [hn]
    simp
  · rintro ⟨n, rfl⟩
    exact ⟨fun i ↦ ⟨n * t.marks i, by simp⟩, n, rfl⟩

/-! ### Moving a vector off the affine node -/

/-- Subtract the multiple of the marks that vanishes at the affine node, then read off the
remaining coordinates in the Bourbaki numbering of the finite type. -/
private noncomputable def deleteAffineNode (t : AffineDynkinType) :
    (Fin t.nodes → ℚ) →ₗ[ℚ] (Fin t.finiteType.rank → ℚ) :=
  LinearMap.funLeft ℚ ℚ t.bourbakiNode ∘ₗ
    (LinearMap.id - (LinearMap.proj t.affineNode).smulRight (fun i ↦ (t.marks i : ℚ)))

private lemma deleteAffineNode_apply (v : Fin t.nodes → ℚ) (i : Fin t.finiteType.rank) :
    deleteAffineNode t v i =
      v (t.bourbakiNode i) - v t.affineNode * t.marks (t.bourbakiNode i) := by
  simp [deleteAffineNode]

/-- Extending a vector by zero at the affine node and moving it back off the affine node gives the
vector back. -/
private lemma deleteAffineNode_extend (ht : t.Valid) (x : Fin t.finiteType.rank → ℚ) :
    deleteAffineNode t (Function.extend t.bourbakiNode x 0) = x := by
  have h0 : Function.extend t.bourbakiNode x 0 t.affineNode = 0 :=
    Function.extend_apply' _ _ _ fun ⟨i, hi⟩ ↦ bourbakiNode_ne_affineNode ht i hi
  funext i
  rw [deleteAffineNode_apply, h0, zero_mul, sub_zero,
    (bourbakiNode_injective ht).extend_apply]

/-- Every vector differs from the extension by zero of its image under `deleteAffineNode` by a
multiple of the marks. -/
private lemma extend_deleteAffineNode (ht : t.Valid) (v : Fin t.nodes → ℚ) :
    Function.extend t.bourbakiNode (deleteAffineNode t v) 0 =
      v - v t.affineNode • (fun i ↦ (t.marks i : ℚ)) := by
  funext k
  by_cases hk : k = t.affineNode
  · subst hk
    rw [Function.extend_apply' _ _ _ fun ⟨i, hi⟩ ↦ bourbakiNode_ne_affineNode ht i hi]
    simp
  · obtain ⟨i, rfl⟩ := exists_bourbakiNode_eq ht hk
    rw [(bourbakiNode_injective ht).extend_apply, deleteAffineNode_apply]
    simp

private lemma deleteAffineNode_surjective (ht : t.Valid) :
    Function.Surjective (deleteAffineNode t) :=
  fun x ↦ ⟨_, deleteAffineNode_extend ht x⟩

private lemma ker_deleteAffineNode (ht : t.Valid) :
    LinearMap.ker (deleteAffineNode t) = ℚ ∙ (fun i ↦ (t.marks i : ℚ)) := by
  ext v
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hv
    refine ⟨v t.affineNode, ?_⟩
    have h := extend_deleteAffineNode ht v
    rw [hv, Function.extend_zero] at h
    exact (sub_eq_zero.1 h.symm).symm
  · rintro ⟨c, rfl⟩
    funext i
    simp [deleteAffineNode_apply]

/-- `deleteAffineNode` sends lattice vectors to lattice vectors. -/
private lemma deleteAffineNode_mem {v : Fin t.nodes → ℚ} (hv : ∀ k, ∃ z : ℤ, (z : ℚ) = v k)
    (i : Fin t.finiteType.rank) : ∃ z : ℤ, (z : ℚ) = deleteAffineNode t v i := by
  obtain ⟨z, hz⟩ := hv (t.bourbakiNode i)
  obtain ⟨w, hw⟩ := hv t.affineNode
  refine ⟨z - w * t.marks (t.bourbakiNode i), ?_⟩
  rw [deleteAffineNode_apply, ← hz, ← hw]
  push_cast
  rfl

/-- Extension by zero sends lattice vectors to lattice vectors. -/
private lemma extend_mem {x : Fin t.finiteType.rank → ℚ} (hx : ∀ i, ∃ z : ℤ, (z : ℚ) = x i)
    (k : Fin t.nodes) : ∃ z : ℤ, (z : ℚ) = Function.extend t.bourbakiNode x 0 k := by
  classical
  rw [Function.extend_def]
  split_ifs with h
  · exact hx _
  · exact ⟨0, by simp⟩

/-! ### The radical quotient -/

/-- The rational quotient by the line of the marks, identified with `Fin t.finiteType.rank → ℚ`
through `deleteAffineNode`. -/
private noncomputable def quotientEquiv (ht : t.Valid) (L : IntegralLattice (Fin t.nodes → ℚ))
    (hrad : L.radical = ℚ ∙ (fun i ↦ (t.marks i : ℚ))) :
    ((Fin t.nodes → ℚ) ⧸ L.radical) ≃ₗ[ℚ] (Fin t.finiteType.rank → ℚ) :=
  (Submodule.quotEquivOfEq _ _ (hrad.trans (ker_deleteAffineNode ht).symm)).trans
    ((deleteAffineNode t).quotKerEquivOfSurjective (deleteAffineNode_surjective ht))

private lemma quotientEquiv_mk (ht : t.Valid) (L : IntegralLattice (Fin t.nodes → ℚ))
    (hrad : L.radical = ℚ ∙ (fun i ↦ (t.marks i : ℚ))) (v : Fin t.nodes → ℚ) :
    quotientEquiv ht L hrad (Submodule.Quotient.mk v) = deleteAffineNode t v := by
  simp [quotientEquiv]

/-- Each class modulo the line of the marks is represented by the extension by zero of its image
under `deleteAffineNode`. -/
private lemma mk_eq_mk_extend_deleteAffineNode (ht : t.Valid)
    (L : IntegralLattice (Fin t.nodes → ℚ))
    (hrad : L.radical = ℚ ∙ (fun i ↦ (t.marks i : ℚ))) (v : Fin t.nodes → ℚ) :
    (Submodule.Quotient.mk v : _ ⧸ L.radical) =
      Submodule.Quotient.mk (Function.extend t.bourbakiNode (deleteAffineNode t v) 0) := by
  rw [extend_deleteAffineNode ht, Submodule.Quotient.eq, sub_sub_cancel, hrad]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- The isometry identifying the radical quotient of a lattice `L` on `Fin t.nodes → ℚ` with a
lattice `M` on `Fin t.finiteType.rank → ℚ`, when both are the standard integer lattices, the
radical of `L` is spanned by the marks, and the forms agree on vectors extended by zero at the
affine node. It serves the affine root lattice and its negation alike. -/
private noncomputable def radicalQuotientIsometryAux (ht : t.Valid)
    (L : IntegralLattice (Fin t.nodes → ℚ)) (M : IntegralLattice (Fin t.finiteType.rank → ℚ))
    (hrad : L.radical = ℚ ∙ (fun i ↦ (t.marks i : ℚ)))
    (hL : ∀ v, v ∈ L.carrier ↔ ∀ k, ∃ z : ℤ, (z : ℚ) = v k)
    (hM : ∀ x, x ∈ M.carrier ↔ ∀ i, ∃ z : ℤ, (z : ℚ) = x i)
    (hform : ∀ x y, L.form (Function.extend t.bourbakiNode x 0)
      (Function.extend t.bourbakiNode y 0) = M.form x y) :
    Isometry L.radicalQuotient M where
  toIsometryEquiv :=
    { toLinearEquiv := quotientEquiv ht L hrad
      map_app' := by
        intro x y
        induction x using Submodule.Quotient.induction_on with | _ x =>
        induction y using Submodule.Quotient.induction_on with | _ y =>
        calc
          _ = M.form (quotientEquiv ht L hrad (Submodule.Quotient.mk x))
              (quotientEquiv ht L hrad (Submodule.Quotient.mk y)) := rfl
          _ = L.radicalQuotient.form (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) := by
            rw [quotientEquiv_mk, quotientEquiv_mk, radicalQuotient_form,
              mk_eq_mk_extend_deleteAffineNode ht L hrad x,
              mk_eq_mk_extend_deleteAffineNode ht L hrad y, radicalQuotientForm_mk, hform] }
  map_carrier := by
    ext x
    simp only [Submodule.mem_map, radicalQuotient_carrier, mem_radicalQuotientCarrier_iff, hM]
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact deleteAffineNode_mem ((hL v).1 hv)
    · intro hx
      refine ⟨Submodule.Quotient.mk (Function.extend t.bourbakiNode x 0),
        ⟨_, (hL _).2 (extend_mem hx), rfl⟩, ?_⟩
      exact (quotientEquiv_mk ht L hrad _).trans (deleteAffineNode_extend ht x)

private lemma radicalQuotientIsometryAux_mk (ht : t.Valid)
    (L : IntegralLattice (Fin t.nodes → ℚ)) (M : IntegralLattice (Fin t.finiteType.rank → ℚ))
    (hrad hL hM hform) (v : Fin t.nodes → ℚ) :
    radicalQuotientIsometryAux ht L M hrad hL hM hform (Submodule.Quotient.mk v) =
      fun i ↦ v (t.bourbakiNode i) - v t.affineNode * t.marks (t.bourbakiNode i) :=
  (quotientEquiv_mk ht L hrad v).trans (funext (deleteAffineNode_apply v))

private lemma radicalQuotientIsometryAux_symm_apply (ht : t.Valid)
    (L : IntegralLattice (Fin t.nodes → ℚ)) (M : IntegralLattice (Fin t.finiteType.rank → ℚ))
    (hrad hL hM hform) (x : Fin t.finiteType.rank → ℚ) :
    (radicalQuotientIsometryAux ht L M hrad hL hM hform).symm x =
      Submodule.Quotient.mk (Function.extend t.bourbakiNode x 0) := by
  apply EquivLike.injective (radicalQuotientIsometryAux ht L M hrad hL hM hform)
  rw [Isometry.apply_symm_apply, radicalQuotientIsometryAux_mk,
    ← funext (deleteAffineNode_apply _), deleteAffineNode_extend ht]

/-- Sums against a vector extended by zero at the affine node reduce to sums over the nodes of
the finite type. -/
private lemma sum_extend_mul (ht : t.Valid) (u : Fin t.finiteType.rank → ℚ) (f : Fin t.nodes → ℚ) :
    ∑ k, Function.extend t.bourbakiNode u 0 k * f k = ∑ i, u i * f (t.bourbakiNode i) := by
  rw [← Finset.sum_extend_zero_of_injective (fun i ↦ u i * f (t.bourbakiNode i))
    (bourbakiNode_injective ht) fun _ ↦ Finset.mem_univ _]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases hk : ∃ i, t.bourbakiNode i = k
  · obtain ⟨i, rfl⟩ := hk
    rw [(bourbakiNode_injective ht).extend_apply, (bourbakiNode_injective ht).extend_apply]
  · simp [Function.extend_apply' _ _ _ hk]

/-- The affine root lattice restricts to the finite root lattice on vectors extended by zero at
the affine node. -/
private lemma rootLattice_form_extend (ht : t.Valid) (x y : Fin t.finiteType.rank → ℚ) :
    t.rootLattice.form (Function.extend t.bourbakiNode x 0) (Function.extend t.bourbakiNode y 0) =
      (t.finiteType.rootLattice t.isSimplyLaced_finiteType).form x y := by
  rw [rootLattice_form_apply, DynkinType.rootLattice_form_apply, sum_extend_mul ht]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg (x i * ·) ?_
  have h := sum_extend_mul ht y fun k ↦ ((t.cartanMatrix (t.bourbakiNode i) k : ℤ) : ℚ)
  rw [← cartanMatrix_submatrix_bourbakiNode ht]
  simp only [submatrix_apply]
  rw [Finset.sum_congr rfl fun k _ ↦ mul_comm _ _, h]
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

/-- **The radical quotient of the affine root lattice is the finite root lattice** of the type it
extends. The class of `v` goes to the vector `i ↦ v (b i) - v (a) δ (b i)` of
`TauCeti.AffineDynkinType.radicalQuotientIsometry_mk`, where `a` is the affine node, `b` the
Bourbaki relabelling and `δ` the marks; its inverse extends by zero at the affine node
(`TauCeti.AffineDynkinType.radicalQuotientIsometry_symm_apply`). -/
noncomputable def radicalQuotientIsometry (ht : t.Valid) :
    Isometry t.rootLattice.radicalQuotient (t.finiteType.rootLattice t.isSimplyLaced_finiteType) :=
  radicalQuotientIsometryAux ht _ _ (radical_rootLattice ht) mem_rootLattice_carrier_iff
    (DynkinType.mem_rootLattice_carrier_iff _ _) (rootLattice_form_extend ht)

/-- The radical-quotient isometry moves a representative off the affine node and reads off the
remaining coordinates in the Bourbaki numbering. -/
@[simp]
theorem radicalQuotientIsometry_mk (ht : t.Valid) (v : Fin t.nodes → ℚ) :
    radicalQuotientIsometry ht (Submodule.Quotient.mk v) =
      fun i ↦ v (t.bourbakiNode i) - v t.affineNode * t.marks (t.bourbakiNode i) :=
  radicalQuotientIsometryAux_mk ht _ _ _ _ _ _ v

/-- The inverse radical-quotient isometry extends by zero at the affine node. -/
@[simp]
theorem radicalQuotientIsometry_symm_apply (ht : t.Valid) (x : Fin t.finiteType.rank → ℚ) :
    (radicalQuotientIsometry ht).symm x =
      Submodule.Quotient.mk (Function.extend t.bourbakiNode x 0) :=
  radicalQuotientIsometryAux_symm_apply ht _ _ _ _ _ _ x

/-- The determinant of the radical quotient of the affine root lattice is the determinant of the
Cartan matrix of the finite type it extends. -/
theorem determinant_radicalQuotient_rootLattice (ht : t.Valid) :
    t.rootLattice.radicalQuotient.determinant = t.finiteType.cartanMatrix.det :=
  (radicalQuotientIsometry ht).determinant_eq.trans (DynkinType.determinant_rootLattice _ _)

/-- The radical quotient of the affine root lattice is positive definite. -/
theorem isPosDef_radicalQuotient_rootLattice (ht : t.Valid) :
    t.rootLattice.radicalQuotient.IsPosDef :=
  (radicalQuotientIsometry ht).isPosDef_iff.2 (DynkinType.isPosDef_rootLattice _ _)

/-- **The affine root lattice has signature `(rank, 1, 0)`**, where `rank` is the rank of the
finite type it extends: it is positive semidefinite with a one-dimensional radical. -/
theorem signature_rootLattice (ht : t.Valid) :
    t.rootLattice.signature = (t.finiteType.rank, 1, 0) := by
  have hq := (radicalQuotientIsometry ht).signature_eq
  rw [(DynkinType.isPosDef_rootLattice _ _).signature_eq, DynkinType.finrank_rootLattice,
    signature_radicalQuotient, Prod.mk.injEq, Prod.mk.injEq] at hq
  have hnull : t.rootLattice.sigNull = 1 := by
    rw [sigNull, radical_rootLattice ht]
    exact finrank_span_singleton fun h ↦ by
      simpa using congrFun h t.affineNode
  simp only [signature, hq.1, hnull, hq.2.2]

/-- The affine root lattice is positive semidefinite. -/
theorem isPosSemidef_rootLattice (ht : t.Valid) : t.rootLattice.IsPosSemidef :=
  t.rootLattice.isPosSemidef_iff_sigNeg_eq_zero.2 (congrArg (·.2.2) (signature_rootLattice ht))

/-! ### The negated lattice -/

/-- **The radical quotient of the negated affine root lattice is the negated finite root lattice**,
a negative definite lattice. This is the lattice of a fibre: the components of a reducible fibre of
affine type `t` have intersection matrix `-cartanMatrix t`. The isometry acts on representatives as
`TauCeti.AffineDynkinType.radicalQuotientIsometry` does. -/
noncomputable def negRadicalQuotientIsometry (ht : t.Valid) :
    Isometry (-t.rootLattice).radicalQuotient
      (-t.finiteType.rootLattice t.isSimplyLaced_finiteType) :=
  radicalQuotientIsometryAux ht _ _ ((radical_neg _).trans (radical_rootLattice ht))
    (fun v ↦ by rw [neg_carrier, mem_rootLattice_carrier_iff])
    (fun x ↦ by rw [neg_carrier, DynkinType.mem_rootLattice_carrier_iff])
    fun x y ↦ by rw [neg_form, neg_form, LinearMap.neg_apply, LinearMap.neg_apply,
      LinearMap.neg_apply, LinearMap.neg_apply, rootLattice_form_extend ht]

/-- The radical-quotient isometry of the negated lattice moves a representative off the affine
node and reads off the remaining coordinates in the Bourbaki numbering. -/
@[simp]
theorem negRadicalQuotientIsometry_mk (ht : t.Valid) (v : Fin t.nodes → ℚ) :
    negRadicalQuotientIsometry ht (Submodule.Quotient.mk v) =
      fun i ↦ v (t.bourbakiNode i) - v t.affineNode * t.marks (t.bourbakiNode i) :=
  radicalQuotientIsometryAux_mk ht _ _ _ _ _ _ v

/-- The inverse radical-quotient isometry of the negated lattice extends by zero at the affine
node. -/
@[simp]
theorem negRadicalQuotientIsometry_symm_apply (ht : t.Valid) (x : Fin t.finiteType.rank → ℚ) :
    (negRadicalQuotientIsometry ht).symm x =
      Submodule.Quotient.mk (Function.extend t.bourbakiNode x 0) :=
  radicalQuotientIsometryAux_symm_apply ht _ _ _ _ _ _ x

/-- The radical quotient of the negated affine root lattice is negative definite. -/
theorem isNegDef_radicalQuotient_neg_rootLattice (ht : t.Valid) :
    (-t.rootLattice).radicalQuotient.IsNegDef :=
  (negRadicalQuotientIsometry ht).isNegDef_iff.2
    ((isNegDef_neg_iff _).2 (DynkinType.isPosDef_rootLattice _ _))

/-- The discriminant of the radical quotient of the negated affine root lattice is the absolute
value of the determinant of the Cartan matrix of the finite type it extends. -/
theorem discriminant_radicalQuotient_neg_rootLattice (ht : t.Valid) :
    (-t.rootLattice).radicalQuotient.discriminant = t.finiteType.cartanMatrix.det.natAbs := by
  rw [(negRadicalQuotientIsometry ht).discriminant_eq, discriminant_neg, discriminant_def,
    DynkinType.determinant_rootLattice]

/-! ### Examples

The fibre types `Iₙ₊₁` have the affine type `A n` (with `III` also of type `A 1` and `IV` of
type `A 2`), and `Iₙ₋₄*` has the affine type `D n`. Their root lattices have discriminants `n + 1`
and `4`. -/

example {n : ℕ} (hn : 1 ≤ n) : (-(A n).rootLattice).radicalQuotient.discriminant = n + 1 := by
  rw [(negRadicalQuotientIsometry (valid_A.2 hn)).discriminant_eq, discriminant_neg]
  exact (congrArg discriminant (DynkinType.rootLattice_A n _)).trans
    (discriminant_typeARootLattice n)

example {n : ℕ} (hn : 4 ≤ n) : (-(D n).rootLattice).radicalQuotient.discriminant = 4 := by
  have : NeZero n := ⟨by omega⟩
  rw [(negRadicalQuotientIsometry (valid_D.2 hn)).discriminant_eq, discriminant_neg]
  exact (DynkinType.rootLatticeIsometryCheckerboard n hn _).discriminant_eq.trans
    (discriminant_checkerboardLattice n)

end AffineDynkinType

end TauCeti
