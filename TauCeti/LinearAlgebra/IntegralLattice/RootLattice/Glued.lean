/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Dual
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Index
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.OrthogonalQuotient.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.OrthogonalSum

/-!
# Gluing an orthogonal sum of ADE root lattices along glue words

Let `t : ι → DynkinType` be a finite family of valid simply-laced components, `R` the orthogonal
sum of their root lattices, and `H` a quadratically isotropic subgroup of the module of glue words
`⊕ i, (t i).glueAlphabet`.  Conway--Sloane describe an overlattice of `R` by such a subgroup,
written in the component labels.  This file transports `H` to the discriminant group of `R`
through `TauCeti.DynkinType.glueWordIsometry` and applies the isotropic gluing construction
`TauCeti.IntegralLattice.ofIsotropicSubgroup`, uniformly in the components.

The resulting lattice `R_H = TauCeti.DynkinType.gluedLattice t ht hv H hH` lives in the same
ambient space as `R` and carries the same form.  Its carrier is the inverse image of `H` in the
dual of `R` (`mem_gluedLattice_carrier_iff`), it contains `R` with index `|H|`, it is even and
positive definite of rank `∑ i, rank (t i)`, and it is unimodular exactly when `H` is Lagrangian,
equivalently when `|H|² = |⊕ i, (t i).glueAlphabet|`.  Its discriminant quadratic module is
identified with `H⊥ / H` in glue-word coordinates (`gluedLatticeDiscriminantIsometry`).  Gluing
along the zero subgroup gives `R` back.

Glued lattices are natural in their glue data.  An isometry of orthogonal sums of root lattices
that carries the glue subgroup `H` onto `H'`, read in glue-word coordinates, restricts to an
isometry of the glued lattices.  This applies in particular to componentwise isometries of the root
lattices and to permutations of the components, the two changes of coordinates under which glue
words are natural.

The root sublattice of a glued lattice is computed from the coset minima of the glue words in
`TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.Roots`.

## Main declarations

* `TauCeti.DynkinType.gluedLattice`: the overlattice of the orthogonal sum of root lattices glued
  along an isotropic subgroup of glue words.
* `TauCeti.DynkinType.mem_gluedLattice_carrier_iff`: the carrier is the set of dual vectors whose
  glue word lies in `H`.
* `TauCeti.DynkinType.relIndex_gluedLattice`: the root lattice has index `|H|`.
* `TauCeti.DynkinType.isEven_gluedLattice`, `isPosDef_gluedLattice`, `finrank_gluedLattice`.
* `TauCeti.DynkinType.isUnimodular_gluedLattice_iff`,
  `TauCeti.DynkinType.isUnimodular_gluedLattice_iff_natCard_sq_eq`: the unimodularity criteria.
* `TauCeti.DynkinType.gluedLatticeDiscriminantIsometry`: the isometry `A_(R_H) ≅ H⊥ / H` of
  finite quadratic modules, in glue-word coordinates.
* `TauCeti.DynkinType.gluedLatticeIsometry`: an isometry of the root lattices carrying one glue
  subgroup onto another induces an isometry of the glued lattices.
* `TauCeti.DynkinType.gluedLatticePiIsometry`, `TauCeti.DynkinType.gluedLatticePiCongrLeftIsometry`:
  the isometries of glued lattices induced by componentwise isometries of the root lattices and by
  permutations of the components.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4
  §3 and Chapter 16 §1.
* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4.
-/

public section

namespace TauCeti.DynkinType

open IntegralLattice

universe v

variable {ι : Type v} [Fintype ι] (t : ι → DynkinType) (ht : ∀ i, (t i).IsSimplyLaced)
  (hv : ∀ i, (t i).Valid)

/-- **The overlattice of an orthogonal sum of ADE root lattices glued along glue words.**  For a
quadratically isotropic subgroup `H` of the glue words of the components `t`, this is the even
overlattice of `⊥ i, (t i).rootLattice` cut out by the image of `H` in its discriminant group
under `TauCeti.DynkinType.glueWordIsometry`. -/
noncomputable def gluedLattice
    (H : AddSubgroup (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)))
    (hH : (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).IsIsotropic H) :
    IntegralLattice (∀ i, Fin (t i).rank → ℚ) :=
  (pi fun i ↦ (t i).rootLattice (ht i)).ofIsotropicSubgroup (isEven_pi_rootLattice t ht)
    (H.map (glueWordIsometry t ht hv).toAddEquiv.toAddMonoidHom)
    (((glueWordIsometry t ht hv).isIsotropic_map_iff _ H).mpr hH)

variable (H : AddSubgroup (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)))
  (hH : (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).IsIsotropic H)

/-- The glued lattice is the isotropic gluing of the orthogonal sum of root lattices along the
image of `H` in its discriminant group. -/
theorem gluedLattice_def :
    gluedLattice t ht hv H hH =
      (pi fun i ↦ (t i).rootLattice (ht i)).ofIsotropicSubgroup (isEven_pi_rootLattice t ht)
        (H.map (glueWordIsometry t ht hv).toAddEquiv.toAddMonoidHom)
        (((glueWordIsometry t ht hv).isIsotropic_map_iff _ H).mpr hH) :=
  (rfl)

/-- Gluing keeps the form of the orthogonal sum of root lattices. -/
@[simp]
theorem gluedLattice_form :
    (gluedLattice t ht hv H hH).form = (pi fun i ↦ (t i).rootLattice (ht i)).form :=
  ofIsotropicSubgroup_form _ _ _ _

/-- **The carrier of a glued lattice**: a vector lies in it exactly when it lies in the dual of
the orthogonal sum of root lattices and the glue word of its discriminant class lies in `H`. -/
theorem mem_gluedLattice_carrier_iff (x : ∀ i, Fin (t i).rank → ℚ) :
    x ∈ (gluedLattice t ht hv H hH).carrier ↔
      ∃ hx : x ∈ (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier,
        (glueWordIsometry t ht hv).toAddEquiv.symm (Submodule.Quotient.mk ⟨x, hx⟩) ∈ H := by
  refine (SetLike.ext_iff.mp (ofIsotropicSubgroup_carrier _ _ _ _) x).trans
    ((mem_intermediateCarrierOfDiscriminantSubgroup_iff _ _ x).trans ?_)
  exact exists_congr fun _ ↦ AddSubgroup.mem_map_equiv

/-- The orthogonal sum of root lattices is a sublattice of every lattice glued from it. -/
theorem carrier_le_gluedLattice_carrier :
    (pi fun i ↦ (t i).rootLattice (ht i)).carrier ≤ (gluedLattice t ht hv H hH).carrier :=
  fun _ hx ↦ (SetLike.ext_iff.mp (ofIsotropicSubgroup_carrier _ _ _ _) _).mpr
    (((pi fun i ↦ (t i).rootLattice (ht i)).intermediateCarrierOfDiscriminantSubgroup _).2.1 hx)

/-- **The orthogonal sum of root lattices has index `|H|` in the lattice glued along `H`.** -/
theorem relIndex_gluedLattice :
    (pi fun i ↦ (t i).rootLattice (ht i)).carrier.toAddSubgroup.relIndex
        (gluedLattice t ht hv H hH).carrier.toAddSubgroup = Nat.card H := by
  have hcarrier : (gluedLattice t ht hv H hH).carrier = _ := ofIsotropicSubgroup_carrier _ _ _ _
  rw [hcarrier, ← IntermediateCarrier.index_def,
    IntermediateCarrier.index_intermediateCarrierOfDiscriminantSubgroup]
  exact AddSubgroup.card_map_of_injective (glueWordIsometry t ht hv).toAddEquiv.injective

/-- A glued lattice is nondegenerate. -/
instance isNondegenerate_gluedLattice : (gluedLattice t ht hv H hH).IsNondegenerate :=
  instIsNondegenerateOfIsotropicSubgroup _ _ _ _

/-- **A glued lattice is even.** -/
theorem isEven_gluedLattice : (gluedLattice t ht hv H hH).IsEven :=
  isEven_ofIsotropicSubgroup _ _ _ _

/-- **A glued lattice is positive definite.** -/
theorem isPosDef_gluedLattice : (gluedLattice t ht hv H hH).IsPosDef :=
  (isPosDef_ofIsotropicSubgroup_iff _ _ _ _).mpr (isPosDef_pi_rootLattice t ht)

/-- **A glued lattice has rank `∑ i, rank (t i)`**, the rank of the orthogonal sum of the root
lattices. -/
@[simp]
theorem finrank_gluedLattice :
    Module.finrank ℤ (gluedLattice t ht hv H hH) = ∑ i, (t i).rank := by
  rw [finrank_carrier, ← finrank_carrier (pi fun i ↦ (t i).rootLattice (ht i)),
    finrank_pi_rootLattice]

/-- **A glued lattice is unimodular exactly when its glue subgroup is Lagrangian.** -/
theorem isUnimodular_gluedLattice_iff :
    (gluedLattice t ht hv H hH).IsUnimodular ↔
      (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).IsLagrangian H := by
  refine (isUnimodular_ofIsotropicSubgroup_iff_isLagrangian _ _ _ _).trans
    (Iff.trans ?_ ((glueWordIsometry t ht hv).isLagrangian_map_iff _ H))
  exact ⟨fun h ↦ (FiniteQuadraticModule.isLagrangian_def _ _).mpr
      ⟨((glueWordIsometry t ht hv).isIsotropic_map_iff _ H).mpr hH, h⟩,
    fun h ↦ h.toFiniteBilinearModule⟩

/-- **A glued lattice is unimodular exactly when `|H|²` is the number of glue words**, the
discriminant of the orthogonal sum of root lattices. -/
theorem isUnimodular_gluedLattice_iff_natCard_sq_eq :
    (gluedLattice t ht hv H hH).IsUnimodular ↔
      Nat.card H ^ 2 = Nat.card (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)) := by
  rw [isUnimodular_gluedLattice_iff]
  exact ⟨fun h ↦ FiniteBilinearModule.IsLagrangian.card_sq _ h.toFiniteBilinearModule
      (isNondegenerate_pi_glueAlphabet t ht hv),
    hH.isLagrangian_of_card_sq_eq _ (isNondegenerate_pi_glueAlphabet t ht hv)⟩

/-- Gluing along the zero subgroup of glue words returns the orthogonal sum of root lattices. -/
@[simp]
theorem gluedLattice_bot :
    gluedLattice t ht hv ⊥ (FiniteQuadraticModule.isIsotropic_bot _) =
      pi fun i ↦ (t i).rootLattice (ht i) := by
  -- The isotropy proof depends on the subgroup, so rewrite `H.map _ = ⊥` by generalizing it.
  have key : ∀ K hK, K = ⊥ →
      (pi fun i ↦ (t i).rootLattice (ht i)).ofIsotropicSubgroup (isEven_pi_rootLattice t ht) K hK =
        pi fun i ↦ (t i).rootLattice (ht i) := by
    rintro _ _ rfl
    exact ofIsotropicSubgroup_bot _ _
  exact key _ _ (AddSubgroup.map_bot _)

/-! ## The discriminant form -/

/-- The glued lattice is the lattice carried by the even intermediate carrier attached to
the image of `H`.  This is `IntegralLattice.ofIsotropicSubgroup_eq_toIntegralLattice` with the
inverse-image carrier written out, the form that
`IntegralLattice.discriminantOrthogonalQuotientIsometryOfSubgroup` uses. -/
private theorem gluedLattice_eq_toIntegralLattice :
    gluedLattice t ht hv H hH =
      (((pi fun i ↦ (t i).rootLattice (ht i)).isEven_intermediateCarrierOfDiscriminantSubgroup_iff
        (isEven_pi_rootLattice t ht)
        (H.map (glueWordIsometry t ht hv).toAddEquiv.toAddMonoidHom)).mpr
        (((glueWordIsometry t ht hv).isIsotropic_map_iff _ H).mpr
          hH)).isIntegral.toIntegralLattice := by
  refine (ofIsotropicSubgroup_eq_toIntegralLattice _ (isEven_pi_rootLattice t ht)
    ⟨H.map (glueWordIsometry t ht hv).toAddEquiv.toAddMonoidHom,
      ((glueWordIsometry t ht hv).isIsotropic_map_iff _ H).mpr hH⟩).trans ?_
  congr 2
  exact evenIntermediateCarrierOrderIsoIsotropicSubgroup_symm_apply_coe _ _ _

/-- Every dual vector of a glued lattice is a dual vector of the orthogonal sum of root
lattices. -/
theorem dualCarrier_gluedLattice_le :
    (gluedLattice t ht hv H hH).dualCarrier ≤
      (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier := by
  rw [gluedLattice_eq_toIntegralLattice]
  exact IntermediateCarrier.IsIntegral.dualCarrier_le _

/-- The class of a dual vector of a glued lattice in the discriminant group of the
orthogonal sum of root lattices does not depend on the presentation of the glued lattice. -/
private theorem mk_dualCarrierEquiv_ofEq_gluedLattice
    (y : (gluedLattice t ht hv H hH).dualCarrier) :
    (Submodule.Quotient.mk ⟨_, IntermediateCarrier.IsIntegral.dualCarrier_le _
        ((Isometry.ofEq (gluedLattice_eq_toIntegralLattice t ht hv H hH)).dualCarrierEquiv
          y).2⟩ : (pi fun i ↦ (t i).rootLattice (ht i)).DiscriminantGroup) =
      Submodule.Quotient.mk ⟨y, dualCarrier_gluedLattice_le t ht hv H hH y.2⟩ :=
  congrArg Submodule.Quotient.mk (Subtype.ext (by
    rw [Isometry.coe_dualCarrierEquiv_apply, Isometry.ofEq_apply]))

/-- **The discriminant form of a glued lattice in glue-word coordinates**: the isometry
`A_(R_H) ≅ H⊥ / H` of finite quadratic modules, where `H⊥` is the orthogonal complement of `H`
in the module of glue words. -/
noncomputable def gluedLatticeDiscriminantIsometry :
    FiniteQuadraticModule.Isometry
      ((gluedLattice t ht hv H hH).discriminantQuadraticModule
        (isEven_gluedLattice t ht hv H hH))
      ((FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).orthogonalQuotient H hH) :=
  ((Isometry.discriminantQuadraticIsometry
      (Isometry.ofEq (gluedLattice_eq_toIntegralLattice t ht hv H hH))
      (isEven_gluedLattice t ht hv H hH)).trans
    ((pi fun i ↦ (t i).rootLattice (ht i)).discriminantOrthogonalQuotientIsometryOfSubgroup
      (isEven_pi_rootLattice t ht)
      (((glueWordIsometry t ht hv).isIsotropic_map_iff _ H).mpr hH))).trans
    ((glueWordIsometry t ht hv).orthogonalQuotientEquiv hH rfl).symm

/-- **The glue word of a dual vector of a glued lattice is orthogonal to the glue code.**
A dual vector `y` of `R_H` is a dual vector of `R`, and the glue word of its class lies in the
orthogonal complement `H⊥` for the polar pairing on glue words. -/
theorem glueWordIsometry_symm_mk_mem_orthogonalComplement
    (y : (gluedLattice t ht hv H hH).dualCarrier) :
    (glueWordIsometry t ht hv).symm
        (Submodule.Quotient.mk ⟨y, dualCarrier_gluedLattice_le t ht hv H hH y.2⟩) ∈
      (FiniteQuadraticModule.pi fun i ↦
        (t i).glueAlphabet (ht i)).toFiniteBilinearModule.orthogonalComplement H := by
  have hmem := IntermediateCarrier.IsIntegral.dualClassHom_mem_orthogonalComplement _
    ((Isometry.ofEq (gluedLattice_eq_toIntegralLattice t ht hv H hH)).dualCarrierEquiv y)
  rw [discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup,
    IntermediateCarrier.IsIntegral.dualClassHom_apply,
    mk_dualCarrierEquiv_ofEq_gluedLattice] at hmem
  have h := ((FiniteBilinearModule.Isometry.orthogonalComplementEquiv _
    (glueWordIsometry t ht hv).toFiniteBilinearModule H).symm
      ⟨_, by rwa [FiniteQuadraticModule.Isometry.toFiniteBilinearModule_toAddEquiv]⟩).2
  rw [FiniteBilinearModule.Isometry.coe_orthogonalComplementEquiv_symm_apply,
    ← FiniteBilinearModule.Isometry.coe_toAddEquiv,
    FiniteBilinearModule.Isometry.symm_toAddEquiv] at h
  simp only [FiniteQuadraticModule.Isometry.toFiniteBilinearModule_toAddEquiv] at h
  exact h

/-- The discriminant isometry of a glued lattice sends the class of a dual vector `y` to
the class in `H⊥ / H` of the glue word of `y`. -/
@[simp]
theorem gluedLatticeDiscriminantIsometry_mk
    (y : (gluedLattice t ht hv H hH).dualCarrier) :
    gluedLatticeDiscriminantIsometry t ht hv H hH (Submodule.Quotient.mk y) =
      (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).orthogonalQuotientMk H hH
        ⟨_, glueWordIsometry_symm_mk_mem_orthogonalComplement t ht hv H hH y⟩ := by
  have h2 := Isometry.discriminantQuadraticIsometry_mk
    (Isometry.ofEq (gluedLattice_eq_toIntegralLattice t ht hv H hH))
    (isEven_gluedLattice t ht hv H hH) y
  have h3 := discriminantOrthogonalQuotientIsometryOfSubgroup_mk _ (isEven_pi_rootLattice t ht)
    (((glueWordIsometry t ht hv).isIsotropic_map_iff _ H).mpr hH)
    ((Isometry.ofEq (gluedLattice_eq_toIntegralLattice t ht hv H hH)).dualCarrierEquiv y)
  -- Evaluate the three factors of the composite one at a time.
  refine (congrArg (fun z ↦ ((glueWordIsometry t ht hv).orthogonalQuotientEquiv hH rfl).symm
    ((pi fun i ↦ (t i).rootLattice (ht i)).discriminantOrthogonalQuotientIsometryOfSubgroup
      (isEven_pi_rootLattice t ht)
      (((glueWordIsometry t ht hv).isIsotropic_map_iff _ H).mpr hH) z)) h2).trans ?_
  refine (congrArg ((glueWordIsometry t ht hv).orthogonalQuotientEquiv hH rfl).symm h3).trans ?_
  refine (FiniteQuadraticModule.Isometry.orthogonalQuotientEquiv_symm_orthogonalQuotientMk
    _ _ _ _).trans ?_
  exact congrArg _ (Subtype.ext (congrArg (glueWordIsometry t ht hv).symm
    ((IntermediateCarrier.IsIntegral.dualClassHom_apply _ _).trans
      (mk_dualCarrierEquiv_ofEq_gluedLattice t ht hv H hH y))))

/-! ## Naturality of glued lattices

An isometry of orthogonal sums of root lattices which carries one glue subgroup onto another, read
in glue-word coordinates, restricts to an isometry of the glued lattices.  The two changes of
coordinates under which glue words are natural, componentwise isometries of the root lattices and
permutations of the components, are the main instances. -/

section Naturality

variable {κ : Type*} [Fintype κ] {s : κ → DynkinType} {hs : ∀ k, (s k).IsSimplyLaced}
  (hvs : ∀ k, (s k).Valid)
  {H' : AddSubgroup (FiniteQuadraticModule.pi fun k ↦ (s k).glueAlphabet (hs k))}
  (hH' : (FiniteQuadraticModule.pi fun k ↦ (s k).glueAlphabet (hs k)).IsIsotropic H')

/-- **Glued lattices are natural under isometries of the root lattices.**  Let `e` be an isometry
between orthogonal sums of root lattices acting on glue words by `φ`, in the sense that it carries
the discriminant class of each glue word `w` to the class of `φ w`.  If `φ w ∈ H'` exactly when
`w ∈ H`, then `e` restricts to an isometry from the lattice glued along `H` to the lattice glued
along `H'`. -/
noncomputable def gluedLatticeIsometry
    (e : IntegralLattice.Isometry (pi fun i ↦ (t i).rootLattice (ht i))
      (pi fun k ↦ (s k).rootLattice (hs k)))
    (φ : (∀ i, (t i).glueAlphabet (ht i)) → ∀ k, (s k).glueAlphabet (hs k))
    (hφ : ∀ w, e.discriminantQuadraticIsometry (isEven_pi_rootLattice t ht)
      (glueWordIsometry t ht hv w) = glueWordIsometry s hs hvs (φ w))
    (hφH : ∀ w, φ w ∈ H' ↔ w ∈ H) :
    IntegralLattice.Isometry (gluedLattice t ht hv H hH) (gluedLattice s hs hvs H' hH') :=
  e.ofIsotropicSubgroups (isEven_pi_rootLattice t ht) (isEven_pi_rootLattice s hs) _ _ <| by
    have hφ' (w) : e.discriminantGroupEquiv (glueWordIsometry t ht hv w) =
        glueWordIsometry s hs hvs (φ w) :=
      (e.discriminantQuadraticIsometry_apply (isEven_pi_rootLattice t ht) _).symm.trans (hφ w)
    ext y
    simp only [AddSubgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨φ w, (hφH w).mpr hw, (hφ' w).symm⟩
    · rintro ⟨v, hvH, rfl⟩
      -- `φ` is surjective: it is the discriminant equivalence read in glue-word coordinates.
      obtain ⟨w, hw⟩ := EquivLike.surjective (glueWordIsometry t ht hv)
        (e.discriminantGroupEquiv.symm (glueWordIsometry s hs hvs v))
      have hφw : φ w = v := EquivLike.injective (glueWordIsometry s hs hvs) <|
        (hφ' w).symm.trans ((congrArg e.discriminantGroupEquiv hw).trans
          (LinearEquiv.apply_symm_apply _ _))
      exact ⟨_, ⟨w, (hφH w).mp (hφw ▸ hvH), rfl⟩, hφw ▸ hφ' w⟩

/-- The isometry of glued lattices induced by an isometry of the root lattices acts by it. -/
@[simp]
theorem gluedLatticeIsometry_apply
    (e : IntegralLattice.Isometry (pi fun i ↦ (t i).rootLattice (ht i))
      (pi fun k ↦ (s k).rootLattice (hs k)))
    (φ : (∀ i, (t i).glueAlphabet (ht i)) → ∀ k, (s k).glueAlphabet (hs k))
    (hφ : ∀ w, e.discriminantQuadraticIsometry (isEven_pi_rootLattice t ht)
      (glueWordIsometry t ht hv w) = glueWordIsometry s hs hvs (φ w))
    (hφH : ∀ w, φ w ∈ H' ↔ w ∈ H) (x : ∀ i, Fin (t i).rank → ℚ) :
    gluedLatticeIsometry t ht hv H hH hvs hH' e φ hφ hφH x = e x :=
  Isometry.ofIsotropicSubgroups_apply _ _ _ _ _ _ x

end Naturality

section Pi

variable {s : ι → DynkinType} {hs : ∀ i, (s i).IsSimplyLaced} (hvs : ∀ i, (s i).Valid)
  {H' : AddSubgroup (FiniteQuadraticModule.pi fun i ↦ (s i).glueAlphabet (hs i))}
  (hH' : (FiniteQuadraticModule.pi fun i ↦ (s i).glueAlphabet (hs i)).IsIsotropic H')

/-- **Componentwise isometries of root lattices induce isometries of glued lattices.**  Let
`f i` be isometries from the root lattices of `t i` to those of `s i`, acting on glue labels by
`g i`.  If the word `i ↦ g i (w i)` lies in `H'` exactly when `w` lies in `H`, the orthogonal sum
of the `f i` restricts to an isometry from the lattice glued along `H` to the lattice glued along
`H'`. -/
noncomputable def gluedLatticePiIsometry
    (f : ∀ i, IntegralLattice.Isometry ((t i).rootLattice (ht i)) ((s i).rootLattice (hs i)))
    (g : ∀ i, (t i).glueAlphabet (ht i) → (s i).glueAlphabet (hs i))
    (hfg : ∀ i x, (s i).glueAlphabetIsometry (hvs i) (hs i) (g i x) =
      (f i).discriminantQuadraticIsometry ((t i).isEven_rootLattice (ht i))
        ((t i).glueAlphabetIsometry (hv i) (ht i) x))
    (hgH : ∀ w, (fun i ↦ g i (w i)) ∈ H' ↔ w ∈ H) :
    IntegralLattice.Isometry (gluedLattice t ht hv H hH) (gluedLattice s hs hvs H' hH') :=
  gluedLatticeIsometry t ht hv H hH hvs hH' (Isometry.pi f) (fun w i ↦ g i (w i))
    (discriminantQuadraticIsometry_pi_glueWordIsometry t ht hv hvs f g hfg) hgH

/-- The isometry of glued lattices induced by componentwise isometries acts componentwise. -/
@[simp]
theorem gluedLatticePiIsometry_apply
    (f : ∀ i, IntegralLattice.Isometry ((t i).rootLattice (ht i)) ((s i).rootLattice (hs i)))
    (g : ∀ i, (t i).glueAlphabet (ht i) → (s i).glueAlphabet (hs i))
    (hfg : ∀ i x, (s i).glueAlphabetIsometry (hvs i) (hs i) (g i x) =
      (f i).discriminantQuadraticIsometry ((t i).isEven_rootLattice (ht i))
        ((t i).glueAlphabetIsometry (hv i) (ht i) x))
    (hgH : ∀ w, (fun i ↦ g i (w i)) ∈ H' ↔ w ∈ H) (x : ∀ i, Fin (t i).rank → ℚ) (i : ι) :
    gluedLatticePiIsometry t ht hv H hH hvs hH' f g hfg hgH x i = f i (x i) := by
  rw [gluedLatticePiIsometry, gluedLatticeIsometry_apply, Isometry.pi_apply]

end Pi

section PiCongrLeft

variable {κ : Type*} [Fintype κ] (σ : κ ≃ ι)
  {K : AddSubgroup (FiniteQuadraticModule.pi fun k ↦ (t (σ k)).glueAlphabet (ht (σ k)))}
  (hK : (FiniteQuadraticModule.pi fun k ↦ (t (σ k)).glueAlphabet (ht (σ k))).IsIsotropic K)

/-- **Permuting the components induces an isometry of glued lattices.**  For an equivalence
`σ : κ ≃ ι`, if moving the label in position `k` to position `σ k` carries the glue subgroup `K`
of the reindexed components `k ↦ t (σ k)` exactly onto `H`, reindexing the orthogonal sum of root
lattices restricts to an isometry from the lattice glued along `K` to the lattice glued along
`H`. -/
noncomputable def gluedLatticePiCongrLeftIsometry
    (hσ : ∀ w, Equiv.piCongrLeft (fun i ↦ (t i).glueAlphabet (ht i)) σ w ∈ H ↔ w ∈ K) :
    IntegralLattice.Isometry (gluedLattice (fun k ↦ t (σ k)) (fun k ↦ ht (σ k))
      (fun k ↦ hv (σ k)) K hK) (gluedLattice t ht hv H hH) :=
  gluedLatticeIsometry (fun k ↦ t (σ k)) (fun k ↦ ht (σ k)) (fun k ↦ hv (σ k)) K hK hv hH
    (Isometry.piCongrLeft (fun i ↦ (t i).rootLattice (ht i)) σ)
    (Equiv.piCongrLeft (fun i ↦ (t i).glueAlphabet (ht i)) σ)
    (discriminantQuadraticIsometry_piCongrLeft_glueWordIsometry t ht hv σ) hσ

/-- The isometry of glued lattices induced by a permutation of the components moves the
coordinates in position `k` to position `σ k`. -/
@[simp]
theorem gluedLatticePiCongrLeftIsometry_apply
    (hσ : ∀ w, Equiv.piCongrLeft (fun i ↦ (t i).glueAlphabet (ht i)) σ w ∈ H ↔ w ∈ K)
    (x : ∀ k, Fin (t (σ k)).rank → ℚ) (k : κ) :
    gluedLatticePiCongrLeftIsometry t ht hv H hH σ hK hσ x (σ k) = x k := by
  rw [gluedLatticePiCongrLeftIsometry, gluedLatticeIsometry_apply,
    Isometry.piCongrLeft_apply_apply]

end PiCongrLeft

end TauCeti.DynkinType
