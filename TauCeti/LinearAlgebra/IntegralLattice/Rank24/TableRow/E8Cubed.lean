/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.CoordinatePower
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Niemeier
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.D8Plus.Isometry
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeE.Roots

/-!
# The table row `E₈³` and its 720-root shell

The row `E₈³` (`TauCeti.RootfulNiemeierType.e8Cubed`) of Conway--Sloane's Table 16.1 has three
`E₈` components and printed glue generator `[000]`.  Because each `E₈` component is already even
and unimodular, its glue alphabet is trivial; the module of glue words of the row has a single
element, and the generated glue subgroup is `⊥`.  Conversely, every other row of the rootful
rank-24 table lists a nonzero printed glue word, so `E₈³` is the unique row whose glue subgroup is
trivial (`TauCeti.RootfulNiemeierType.glueSubgroup_eq_bot_iff_eq_e8Cubed`) and equivalently the
unique row whose uniform table lattice `r.lattice` coincides with the orthogonal sum `r.rootLattice`
of its component root lattices
(`TauCeti.RootfulNiemeierType.lattice_eq_rootLattice_iff_eq_e8Cubed`).

Constructed through the uniform gluing API rather than as an ad hoc constant, the named lattice
`TauCeti.e8CubedLattice` has the literal carrier consisting of families of three rational
8-vectors whose twenty-four Bourbaki simple-root coordinates are all integers
(`TauCeti.mem_e8CubedLattice_carrier_iff`).  Two explicit coordinate-power isometries connect this
table lattice to standard models on `Fin 3 → Fin 8 → ℚ`:

* `TauCeti.e8CubedSimpleRootIsometry` identifies `TauCeti.e8CubedLattice` with the coordinate power
  `TauCeti.IntegralLattice.typeE₈RootLattice.coordinatePower (Fin 3)`, keeping every simple-root
  coordinate;
* `TauCeti.e8CubedD8PlusIsometry` identifies `TauCeti.e8CubedLattice` with Conway--Sloane's
  Euclidean block model `(checkerboardPlusLattice 8 _).coordinatePower (Fin 3)`, carrying each
  block's simple roots to the Bourbaki--Conway--Sloane vectors `e8GlueRoot` of
  `D₈⁺ = D₈ ∪ (s + D₈)` and intertwining the lattice form with the standard 24-dimensional dot
  product (`TauCeti.sum_mul_e8CubedD8PlusIsometry`).

Unlike rows with nontrivial glue vectors, `TauCeti.e8CubedLattice` is spanned over `ℤ` by its own
norm-`2` shell (`TauCeti.span_vectorsOfNorm_two_e8CubedLattice_eq_top`).  Combining the orthogonal
norm-shell decomposition of `TauCeti.IntegralLattice.piVectorsOfNormTwoEquiv` with the 240-root
Bourbaki enumeration `TauCeti.IntegralLattice.typeE₈RootEquiv` yields the explicit 720-root shell
equivalence `TauCeti.e8CubedRootEquiv`, from which the minimum `2`, the norm-`2` representation
number `720`, and the kissing number `720` follow.

## Main declarations

* `TauCeti.e8CubedLattice`: stable name for `RootfulNiemeierType.e8Cubed.lattice`, reducible so the
  uniform row theorems (`isEven_lattice`, `isPosDef_lattice`, `finrank_lattice`) apply directly,
  with `TauCeti.e8CubedLattice_eq_rootLattice`.
* `TauCeti.mem_e8CubedLattice_carrier_iff`: literal integer-coordinate characterization of the
  table carrier.
* `TauCeti.e8CubedSimpleRootIsometry`: explicit isometry onto
  `typeE₈RootLattice.coordinatePower (Fin 3)`.
* `TauCeti.e8CubedD8PlusIsometry`: explicit isometry onto Conway--Sloane's Euclidean block power
  `(checkerboardPlusLattice 8 _).coordinatePower (Fin 3)`.
* `TauCeti.isUnimodular_e8CubedLattice`, `TauCeti.discriminant_e8CubedLattice`,
  `TauCeti.determinant_e8CubedLattice`: unimodularity, discriminant `1`, and determinant `1`.
* `TauCeti.span_vectorsOfNorm_two_e8CubedLattice_eq_top`: the norm-`2` roots span the whole lattice.
* `TauCeti.e8CubedRootVector`, `TauCeti.e8CubedRootEquiv`: explicit 720-vector enumeration of the
  norm-`2` shell `e8CubedLattice.vectorsOfNorm 2`.
* `TauCeti.minimum_e8CubedLattice`, `TauCeti.representationNumber_e8CubedLattice_two`,
  `TauCeti.kissingNumber_e8CubedLattice`: minimum `2` and kissing number `720`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VII.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4,
  §8.1, and Chapter 16, §1, Table 16.1.
* W. Ebeling, *Lattices and Codes*, 3rd ed., Chapters 1--3.
-/

public section

namespace TauCeti

namespace RootfulNiemeierType

open DynkinType

/-! ### Components of the row -/

/-- The row `E₈³` has three components. -/
@[simp]
theorem length_components_e8Cubed : e8Cubed.components.length = 3 :=
  List.length_replicate

/-- Every component of the row `E₈³` has type `E₈`. -/
@[simp]
theorem componentType_e8Cubed (i : Fin e8Cubed.components.length) :
    e8Cubed.componentType i = E8 :=
  congrArg Subtype.val (List.getElem_replicate _)

end RootfulNiemeierType

/-! ### The named lattice `e8CubedLattice` and its literal carrier -/

/-- **The `E₈³` Niemeier lattice**, constructed through the uniform gluing API from the `E₈³` row
of the rootful rank-24 table.

Because `e8CubedLattice` is reducible to `RootfulNiemeierType.e8Cubed.lattice`, the uniform row
theorems (`isEven_lattice`, `isPosDef_lattice`, `finrank_lattice`, `isNondegenerate_lattice`) apply
directly. -/
noncomputable abbrev e8CubedLattice :
    IntegralLattice (∀ i, Fin (RootfulNiemeierType.e8Cubed.componentType i).rank → ℚ) :=
  RootfulNiemeierType.e8Cubed.lattice

/-- Because the glue subgroup of `E₈³` is trivial, `e8CubedLattice` is literally the orthogonal
sum of the three component `E₈` root lattices. -/
theorem e8CubedLattice_eq_rootLattice :
    e8CubedLattice = RootfulNiemeierType.e8Cubed.rootLattice :=
  (RootfulNiemeierType.lattice_eq_rootLattice_iff_eq_e8Cubed .e8Cubed).mpr rfl

/-- **Literal carrier of `e8CubedLattice`**: a family of three rational vectors lies in the table
lattice `E₈³` if and only if all twenty-four of its Bourbaki simple-root coordinates are
integers. -/
theorem mem_e8CubedLattice_carrier_iff
    (x : ∀ i, Fin (RootfulNiemeierType.e8Cubed.componentType i).rank → ℚ) :
    x ∈ e8CubedLattice.carrier ↔ ∀ i j, ∃ z : ℤ, (z : ℚ) = x i j := by
  rw [e8CubedLattice_eq_rootLattice, IntegralLattice.mem_pi_carrier_iff]
  exact forall_congr' fun i ↦ DynkinType.mem_rootLattice_carrier_iff _ _ (x i)

/-! ### Simple-root coordinate-power model -/

/-- **The table lattice `E₈³` is the coordinate power `E₈³` in Bourbaki simple-root coordinates**:
an explicit isometry onto `typeE₈RootLattice.coordinatePower (Fin 3)` keeping every coordinate. -/
noncomputable def e8CubedSimpleRootIsometry :
    IntegralLattice.Isometry e8CubedLattice
      (IntegralLattice.typeE₈RootLattice.coordinatePower (Fin 3)) :=
  (IntegralLattice.Isometry.ofEq e8CubedLattice_eq_rootLattice).trans <|
    (IntegralLattice.Isometry.piCongrLeft
        (fun i ↦ (RootfulNiemeierType.e8Cubed.componentType i).rootLattice
          (RootfulNiemeierType.e8Cubed.isSimplyLaced_componentType i))
        (finCongr RootfulNiemeierType.length_components_e8Cubed.symm)).symm.trans <|
      IntegralLattice.Isometry.pi fun _ : Fin 3 ↦
        ((RootfulNiemeierType.e8Cubed.componentType _).rootLatticeIsometryOfEq _
            (RootfulNiemeierType.componentType_e8Cubed _) DynkinType.isSimplyLaced_E8).trans
          (IntegralLattice.Isometry.ofEq (DynkinType.rootLattice_E8 DynkinType.isSimplyLaced_E8))

/-- `e8CubedSimpleRootIsometry` reads coordinate `(k, j)` on `Fin 3 × Fin 8` directly from the
corresponding table coordinate. -/
theorem e8CubedSimpleRootIsometry_apply
    (x : ∀ i, Fin (RootfulNiemeierType.e8Cubed.componentType i).rank → ℚ)
    (k : Fin 3) (j : Fin 8) :
    e8CubedSimpleRootIsometry x k j =
      x (Fin.cast RootfulNiemeierType.length_components_e8Cubed.symm k)
        (Fin.cast (congrArg DynkinType.rank
          (RootfulNiemeierType.componentType_e8Cubed _)).symm j) := by
  rw [e8CubedSimpleRootIsometry]
  simp only [IntegralLattice.Isometry.trans_apply, IntegralLattice.Isometry.pi_apply,
    IntegralLattice.Isometry.piCongrLeft_symm_apply, IntegralLattice.Isometry.ofEq_apply]
  -- `rootLattice_E8` equates lattices on `Fin E8.rank → ℚ` and `Fin 8 → ℚ`, whose `Module`
  -- instances and index types agree at semireducible rather than `simp`'s instance transparency.
  exact (congrFun (IntegralLattice.Isometry.trans_apply _ _ _) j).trans <|
    (congrFun (IntegralLattice.Isometry.ofEq_apply (DynkinType.rootLattice_E8 _) _) j).trans <|
      DynkinType.rootLatticeIsometryOfEq_apply (s := .E8) _ _ _ _ _ j

/-- The inverse of `e8CubedSimpleRootIsometry` writes a triple of `E₈` vectors into the table
coordinates. -/
theorem e8CubedSimpleRootIsometry_symm_apply
    (y : Fin 3 → Fin 8 → ℚ)
    (i : Fin RootfulNiemeierType.e8Cubed.components.length)
    (j : Fin (RootfulNiemeierType.e8Cubed.componentType i).rank) :
    e8CubedSimpleRootIsometry.symm y i j =
      y (Fin.cast RootfulNiemeierType.length_components_e8Cubed i)
        (Fin.cast (congrArg DynkinType.rank
          (RootfulNiemeierType.componentType_e8Cubed i)) j) := by
  have key := e8CubedSimpleRootIsometry_apply (e8CubedSimpleRootIsometry.symm y)
    (Fin.cast RootfulNiemeierType.length_components_e8Cubed i)
    (Fin.cast (congrArg DynkinType.rank (RootfulNiemeierType.componentType_e8Cubed i)) j)
  rw [e8CubedSimpleRootIsometry.apply_symm_apply] at key
  refine Eq.trans ?_ key.symm
  have hcast : ∀ (i' : Fin RootfulNiemeierType.e8Cubed.components.length) (hi : i' = i)
      (j' : Fin (RootfulNiemeierType.e8Cubed.componentType i').rank),
      j'.1 = j.1 →
      e8CubedSimpleRootIsometry.symm y i j = e8CubedSimpleRootIsometry.symm y i' j' := by
    rintro _ rfl j' hj
    exact congrArg _ (Fin.ext hj.symm)
  exact hcast _ (Fin.ext rfl) _ rfl

/-! ### Conway--Sloane Euclidean `(D₈⁺)³` block model -/

/-- **The table lattice `E₈³` in Conway--Sloane Euclidean coordinates**: an explicit isometry onto
`(D₈⁺)³ = (checkerboardPlusLattice 8 _).coordinatePower (Fin 3)`, acting on each 8-coordinate
block by `TauCeti.IntegralLattice.typeE₈IsometryD8Plus`. -/
noncomputable def e8CubedD8PlusIsometry :
    IntegralLattice.Isometry e8CubedLattice
      ((IntegralLattice.checkerboardPlusLattice 8 (by decide)).coordinatePower (Fin 3)) :=
  e8CubedSimpleRootIsometry.trans
    (IntegralLattice.Isometry.pi fun _ : Fin 3 ↦ IntegralLattice.typeE₈IsometryD8Plus)

/-- On each block `k : Fin 3`, `e8CubedD8PlusIsometry` applies the Bourbaki--Conway--Sloane
comparison map `e8GlueMap` to the `k`-th simple-root block. -/
theorem e8CubedD8PlusIsometry_apply
    (x : ∀ i, Fin (RootfulNiemeierType.e8Cubed.componentType i).rank → ℚ) (k : Fin 3) :
    e8CubedD8PlusIsometry x k =
      IntegralLattice.e8GlueMap (e8CubedSimpleRootIsometry x k) := by
  rw [e8CubedD8PlusIsometry, IntegralLattice.Isometry.trans_apply,
    IntegralLattice.Isometry.pi_apply, IntegralLattice.typeE₈IsometryD8Plus_apply]

/-- On the `j`-th simple root of block `k`, `e8CubedD8PlusIsometry` produces the `j`-th Bourbaki
glue root `e8GlueRoot j` of `D₈⁺` supported in block `k`. -/
@[simp]
theorem e8CubedD8PlusIsometry_e8CubedSimpleRootIsometry_symm_single_typeE₈SimpleRoot
    (k : Fin 3) (j : Fin 8) :
    e8CubedD8PlusIsometry
        (e8CubedSimpleRootIsometry.symm (Pi.single k (IntegralLattice.typeE₈SimpleRoot j))) =
      Pi.single k (IntegralLattice.e8GlueRoot j) := by
  ext m c
  rw [e8CubedD8PlusIsometry_apply, e8CubedSimpleRootIsometry.apply_symm_apply]
  rcases eq_or_ne m k with rfl | hmk
  · simp [IntegralLattice.e8GlueMap_typeE₈SimpleRoot]
  · simp [Pi.single_eq_of_ne hmk]

/-- **The Conway--Sloane Euclidean dot product computes the bilinear form of `e8CubedLattice`**:
the sum of coordinate products across all three 8-blocks equals `e8CubedLattice.form x y`. -/
theorem sum_mul_e8CubedD8PlusIsometry
    (x y : ∀ i, Fin (RootfulNiemeierType.e8Cubed.componentType i).rank → ℚ) :
    (∑ k : Fin 3, ∑ j : Fin 8,
        e8CubedD8PlusIsometry x k j * e8CubedD8PlusIsometry y k j) =
      e8CubedLattice.form x y := by
  rw [← e8CubedD8PlusIsometry.map_app x y, IntegralLattice.pi_form,
    IntegralLattice.piForm_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [IntegralLattice.checkerboardPlusLattice_form,
    IntegralLattice.checkerboardLattice_form_apply]

/-! ### Unimodularity, root generation, and the 720-root shell -/

/-- **The `E₈³` Niemeier lattice is unimodular.** -/
theorem isUnimodular_e8CubedLattice : e8CubedLattice.IsUnimodular :=
  RootfulNiemeierType.isUnimodular_lattice_of_ne .e8Cubed
    (by decide) (by decide) (by decide) (by decide)

/-- The discriminant of `e8CubedLattice` is `1`. -/
@[simp]
theorem discriminant_e8CubedLattice : e8CubedLattice.discriminant = 1 :=
  e8CubedLattice.isUnimodular_iff_discriminant_eq_one.mp isUnimodular_e8CubedLattice

/-- The signed determinant of `e8CubedLattice` is `1`. -/
@[simp]
theorem determinant_e8CubedLattice : e8CubedLattice.determinant = 1 := by
  have hsig : e8CubedLattice.sigNeg = 0 :=
    e8CubedLattice.isPosSemidef_iff_sigNeg_eq_zero.mp
      (RootfulNiemeierType.isPosDef_lattice .e8Cubed).isPosSemidef
  rw [e8CubedLattice.determinant_eq_neg_one_pow_sigNeg_mul_discriminant, hsig,
    discriminant_e8CubedLattice]
  norm_num

/-- In the ambient space, the norm-`2` vectors of `e8CubedLattice` span its entire carrier. -/
theorem span_vectorsOfNorm_two_e8CubedLattice :
    Submodule.span ℤ
        ((fun x : e8CubedLattice ↦
          (x : ∀ i, Fin (RootfulNiemeierType.e8Cubed.componentType i).rank → ℚ)) ''
          e8CubedLattice.vectorsOfNorm 2) =
      e8CubedLattice.carrier :=
  (RootfulNiemeierType.span_vectorsOfNorm_two_lattice_of_ne .e8Cubed
      (by decide) (by decide) (by decide) (by decide)).trans
    (congrArg IntegralLattice.carrier e8CubedLattice_eq_rootLattice.symm)

/-- **Unlike rows with nontrivial glue, `e8CubedLattice` is generated over `ℤ` by its norm-`2`
roots.** -/
theorem span_vectorsOfNorm_two_e8CubedLattice_eq_top :
    Submodule.span ℤ (e8CubedLattice.vectorsOfNorm 2) = ⊤ := by
  apply Submodule.map_injective_of_injective e8CubedLattice.carrier.injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  exact span_vectorsOfNorm_two_e8CubedLattice

/-- The `(k, r)`-th root of `e8CubedLattice`, obtained by placing the `r`-th Bourbaki root of
`typeE₈RootLattice` in component `k : Fin 3`. -/
noncomputable def e8CubedRootVector (k : Fin 3) (r : Fin 240) : e8CubedLattice :=
  e8CubedSimpleRootIsometry.carrierEquiv.symm
    ⟨Pi.single k (IntegralLattice.typeE₈RootVector r : Fin 8 → ℚ),
      IntegralLattice.single_mem_pi_carrier _ k (IntegralLattice.typeE₈RootVector r).2⟩

/-- In simple-root coordinates, `e8CubedRootVector k r` is `typeE₈RootVector r` supported in
component `k`. -/
@[simp]
theorem e8CubedSimpleRootIsometry_e8CubedRootVector (k : Fin 3) (r : Fin 240) :
    e8CubedSimpleRootIsometry (e8CubedRootVector k r) =
      Pi.single k (IntegralLattice.typeE₈RootVector r : Fin 8 → ℚ) := by
  rw [e8CubedRootVector, IntegralLattice.Isometry.coe_carrierEquiv_symm_apply,
    e8CubedSimpleRootIsometry.apply_symm_apply]

/-- Literal table coordinates of `e8CubedRootVector k r`: it agrees with the Bourbaki root
`DynkinType.e8Coroot r` in component `k` and vanishes in the other two components. -/
theorem e8CubedRootVector_apply (k : Fin 3) (r : Fin 240)
    (i : Fin RootfulNiemeierType.e8Cubed.components.length)
    (j : Fin (RootfulNiemeierType.e8Cubed.componentType i).rank) :
    (e8CubedRootVector k r :
        ∀ m, Fin (RootfulNiemeierType.e8Cubed.componentType m).rank → ℚ) i j =
      if Fin.cast RootfulNiemeierType.length_components_e8Cubed i = k then
        (DynkinType.e8Coroot r
          (Fin.cast (congrArg DynkinType.rank
            (RootfulNiemeierType.componentType_e8Cubed i)) j) : ℚ)
      else 0 := by
  rw [e8CubedRootVector, IntegralLattice.Isometry.coe_carrierEquiv_symm_apply,
    e8CubedSimpleRootIsometry_symm_apply]
  by_cases hik : Fin.cast RootfulNiemeierType.length_components_e8Cubed i = k <;> simp [hik]

/-- In Conway--Sloane `(D₈⁺)³` coordinates, `e8CubedRootVector k r` is the Euclidean root
`e8GlueMap (typeE₈RootVector r)` supported in block `k`. -/
@[simp]
theorem e8CubedD8PlusIsometry_e8CubedRootVector (k : Fin 3) (r : Fin 240) :
    e8CubedD8PlusIsometry (e8CubedRootVector k r) =
      Pi.single k (IntegralLattice.e8GlueMap (IntegralLattice.typeE₈RootVector r)) := by
  ext m c
  rw [e8CubedD8PlusIsometry_apply, e8CubedSimpleRootIsometry_e8CubedRootVector]
  rcases eq_or_ne m k with rfl | hmk
  · simp
  · simp [Pi.single_eq_of_ne hmk]

/-- Every enumerated root `e8CubedRootVector k r` has norm `2`. -/
@[simp]
theorem norm_e8CubedRootVector (k : Fin 3) (r : Fin 240) :
    e8CubedLattice.norm (e8CubedRootVector k r) = 2 := by
  rw [IntegralLattice.norm_apply, ← e8CubedSimpleRootIsometry.map_app,
    ← IntegralLattice.norm_apply, e8CubedSimpleRootIsometry_e8CubedRootVector,
    IntegralLattice.norm_pi_single, IntegralLattice.norm_typeE₈RootVector]

/-- Every enumerated root `e8CubedRootVector k r` has integral norm `2`. -/
@[simp]
theorem integralNorm_e8CubedRootVector (k : Fin 3) (r : Fin 240) :
    e8CubedLattice.integralNorm (e8CubedRootVector k r) = 2 := by
  exact_mod_cast (e8CubedLattice.integralNorm_cast _).trans (norm_e8CubedRootVector k r)

/-- **Explicit 720-element enumeration of the norm-`2` shell of `e8CubedLattice`**, decomposing the
shell across the three `E₈` summands via `piVectorsOfNormTwoEquiv` and indexing each summand shell
by `typeE₈RootEquiv`. -/
noncomputable def e8CubedRootEquiv :
    Fin 3 × Fin 240 ≃ e8CubedLattice.vectorsOfNorm 2 :=
  ((Equiv.prodCongr (Equiv.refl (Fin 3)) IntegralLattice.typeE₈RootEquiv).trans
      (Equiv.sigmaEquivProd (Fin 3) (IntegralLattice.typeE₈RootLattice.vectorsOfNorm 2)).symm).trans
    ((IntegralLattice.piVectorsOfNormTwoEquiv
        (fun _ : Fin 3 ↦ IntegralLattice.typeE₈RootLattice)
        (fun _ ↦ IntegralLattice.isEven_typeE₈RootLattice)
        (fun _ ↦ IntegralLattice.isPosDef_typeE₈RootLattice)).trans
      (e8CubedSimpleRootIsometry.symm.carrierEquiv.toEquiv.subtypeEquiv fun y ↦
        (e8CubedSimpleRootIsometry.symm.carrierEquiv_mem_vectorsOfNorm_iff y 2).symm))

/-- `e8CubedRootEquiv` sends `(k, r)` to `e8CubedRootVector k r`. -/
@[simp]
theorem coe_e8CubedRootEquiv_apply (p : Fin 3 × Fin 240) :
    (e8CubedRootEquiv p : e8CubedLattice) = e8CubedRootVector p.1 p.2 := by
  apply Subtype.ext
  rw [e8CubedRootEquiv, e8CubedRootVector]
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst, Prod.map_snd,
    id_eq, Equiv.sigmaEquivProd_symm_apply, Equiv.subtypeEquiv_apply, LinearEquiv.coe_toEquiv,
    IntegralLattice.Isometry.coe_carrierEquiv_apply,
    IntegralLattice.Isometry.coe_carrierEquiv_symm_apply,
    IntegralLattice.coe_piVectorsOfNormTwoEquiv_apply, IntegralLattice.typeE₈RootEquiv_apply]

/-- Distinct `(k, r)` pairs give distinct root vectors in `e8CubedLattice`. -/
theorem e8CubedRootVector_injective :
    Function.Injective (Function.uncurry e8CubedRootVector) := fun p q h ↦
  e8CubedRootEquiv.injective <| Subtype.ext <|
    (coe_e8CubedRootEquiv_apply p).trans (h.trans (coe_e8CubedRootEquiv_apply q).symm)

/-- A vector of `e8CubedLattice` has norm `2` if and only if it is one of the 720 enumerated
roots `e8CubedRootVector k r`. -/
theorem norm_e8CubedLattice_eq_two_iff (x : e8CubedLattice) :
    e8CubedLattice.norm x = 2 ↔ ∃ k r, e8CubedRootVector k r = x := by
  rw [← IntegralLattice.mem_vectorsOfNorm]
  constructor
  · intro hx
    obtain ⟨⟨k, r⟩, hkr⟩ := e8CubedRootEquiv.surjective ⟨x, hx⟩
    exact ⟨k, r, (coe_e8CubedRootEquiv_apply (k, r)).symm.trans (congrArg Subtype.val hkr)⟩
  · rintro ⟨k, r, rfl⟩
    rw [← coe_e8CubedRootEquiv_apply (k, r)]
    exact (e8CubedRootEquiv (k, r)).2

/-- **The minimum of `e8CubedLattice` is `2`.** -/
@[simp]
theorem minimum_e8CubedLattice : e8CubedLattice.minimum = 2 :=
  (RootfulNiemeierType.isPosDef_lattice .e8Cubed).minimum_eq_two
    (RootfulNiemeierType.isEven_lattice .e8Cubed) (integralNorm_e8CubedRootVector 0 0)

/-- **`e8CubedLattice` has `720` vectors of norm `2`**, agreeing with the table root count
`3 × 240 = 720`. -/
@[simp]
theorem representationNumber_e8CubedLattice_two :
    e8CubedLattice.representationNumber 2 = 720 := by
  rw [e8CubedSimpleRootIsometry.representationNumber_eq 2,
    IntegralLattice.representationNumber_pi_two
      (fun _ : Fin 3 ↦ IntegralLattice.typeE₈RootLattice)
      (fun _ ↦ IntegralLattice.isEven_typeE₈RootLattice)
      (fun _ ↦ IntegralLattice.isPosDef_typeE₈RootLattice)]
  simp [IntegralLattice.representationNumber_typeE₈RootLattice_two]

/-- **The kissing number of `e8CubedLattice` is `720`.** -/
@[simp]
theorem kissingNumber_e8CubedLattice : e8CubedLattice.kissingNumber = 720 := by
  rw [IntegralLattice.kissingNumber_eq_representationNumber (by simp [minimum_e8CubedLattice]),
    minimum_e8CubedLattice]
  exact representationNumber_e8CubedLattice_two

end TauCeti
