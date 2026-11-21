/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Unramified

/-!
# The maximal extension unramified outside a set of places

Let `F / k` be an algebraic function field, `A / F` an algebraic extension, for instance an
algebraic closure of `F`, and `S` a set of places of `F`. A subextension `E` of `A / F` is
**unramified outside `S`** when it is finite and separable over `F` and its branch places, the
places of `F` not unramified in `E`, all lie in `S` (`IntermediateField.IsUnramifiedOutside`).
The compositum of all of them is the **maximal subextension of `A / F` unramified outside `S`**
(`TauCeti.maximalUnramifiedOutside`). For `F = k(t)` with `k` algebraically closed and `S` the
three places `t = 0`, `t = 1`, `t = ∞`, its Galois group is the geometric fundamental group of the
projective line minus three points, realized field-theoretically.

The finite subextensions unramified outside `S` are closed under composita
(`IntermediateField.IsUnramifiedOutside.sup`, from Stichtenoth's Corollary 3.9.3,
`TauCeti.Place.isUnramified_sup_iff`) and under passing to smaller fields
(`IntermediateField.IsUnramifiedOutside.mono`, from multiplicativity of ramification in towers).
A finite subextension of `A / F` lies in a finite compositum of members of the family as soon as it
lies in the full compositum, since it is finitely generated. Hence the finite subextensions of the
maximal one are exactly the finite subextensions unramified outside `S`
(`TauCeti.le_maximalUnramifiedOutside_iff`).

Unramifiedness outside `S` is invariant under isomorphism over `F`, so every `F`-embedding of `A`
into itself maps the maximal subextension into itself. When `A / F` is normal this makes it a
Galois extension of `F` (`TauCeti.instIsGaloisMaximalUnramifiedOutside`), and its Galois group,
with the Krull topology, is a profinite group. Through the Galois correspondence of infinite
Galois theory, the open normal subgroups of that group correspond to the finite Galois
subextensions of `A / F` unramified outside `S`
(`TauCeti.maximalUnramifiedOutside.openNormalSubgroupEquiv`).

## Main definitions

* `IntermediateField.IsUnramifiedOutside`: a finite separable subextension whose branch places lie
  in `S`.
* `TauCeti.maximalUnramifiedOutside A S`: the compositum of the subextensions of `A / F`
  unramified outside `S`.
* `TauCeti.maximalUnramifiedOutside.openNormalSubgroupEquiv`: the open normal subgroups of its
  Galois group, matched with the finite Galois subextensions of `A / F`
  (`FiniteGaloisIntermediateField`) unramified outside `S`.

## Main results

* `IntermediateField.IsUnramifiedOutside.isUnramified` and
  `IntermediateField.IsUnramifiedOutside.of_isUnramified`: unramified outside `S` means finite,
  separable and unramified at every place outside `S`.
* `IntermediateField.IsUnramifiedOutside.sup`, `IntermediateField.IsUnramifiedOutside.mono`,
  `IntermediateField.IsUnramifiedOutside.map` and `IntermediateField.isUnramifiedOutside_bot`:
  the family is closed under composita, smaller fields and embeddings, and contains `F`.
* `IntermediateField.IsUnramifiedOutside.mono_set` and `TauCeti.maximalUnramifiedOutside_mono`:
  enlarging `S` keeps a subextension unramified outside it and enlarges the maximal one.
* `TauCeti.le_maximalUnramifiedOutside_iff`: a finite subextension lies in the maximal one
  exactly when it is unramified outside `S`.
* `TauCeti.mem_maximalUnramifiedOutside_iff`: an element lies in the maximal subextension exactly
  when the subextension it generates is unramified outside `S`.
* `TauCeti.instIsGaloisMaximalUnramifiedOutside`: over a normal `A / F`, the maximal subextension
  unramified outside `S` is Galois.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Definition 3.1.13 and Corollary 3.9.3.
* T. Szamuely, *Galois Groups and Fundamental Groups*, Cambridge Studies in Advanced Mathematics
  117, Cambridge University Press, 2009, Section 4.6, for the Galois group of the maximal
  extension of a function field unramified outside finitely many places as a fundamental group.
-/

public noncomputable section

open IntermediateField

variable {k F A : Type*} [Field k] [Field F] [Field A] [Algebra k F] [Algebra F A] [Algebra k A]
  [IsScalarTower k F A]

namespace IntermediateField

section Algebraic

variable [Algebra.IsAlgebraic F A]

/-- A subextension `E` of an algebraic extension `A / F` of a function field `F / k` is
**unramified outside** a set `S` of places of `F` when it is finite and separable over `F` and
its branch places `TauCeti.Place.branchPlaces k E`, the places of `F` not unramified in `E`, all
lie in `S`. -/
structure IsUnramifiedOutside (E : IntermediateField F A) (S : Set (TauCeti.Place k F)) :
    Prop where
  /-- `E` is a finite extension of `F`. -/
  finiteDimensional : FiniteDimensional F E
  /-- `E` is a separable extension of `F`. -/
  isSeparable : Algebra.IsSeparable F E
  /-- Every branch place of `E` over `F` lies in `S`. -/
  branchPlaces_subset : TauCeti.Place.branchPlaces (k := k) (F := F) k E ⊆ S

variable {S : Set (TauCeti.Place k F)} {E E₁ E₂ L : IntermediateField F A}

/-- In a subextension unramified outside `S`, every place of `F` outside `S` is unramified. -/
theorem IsUnramifiedOutside.isUnramified (h : E.IsUnramifiedOutside S) {P : TauCeti.Place k F}
    (hP : P ∉ S) : P.IsUnramified (k' := k) (F' := E) :=
  not_not.mp fun hU ↦ hP (h.branchPlaces_subset (TauCeti.Place.mem_branchPlaces_iff.mpr hU))

/-- A finite separable subextension in which every place of `F` outside `S` is unramified is
unramified outside `S`. -/
theorem IsUnramifiedOutside.of_isUnramified [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (h : ∀ P ∉ S, P.IsUnramified (k' := k) (F' := E)) : E.IsUnramifiedOutside S :=
  ⟨inferInstance, inferInstance, fun P hP ↦
    not_not.mp fun hPS ↦ TauCeti.Place.mem_branchPlaces_iff.mp hP (h P hPS)⟩

/-- **Being unramified outside `S` is invariant under isomorphism over `F`**, also between
subextensions of different algebraic extensions of `F`. -/
theorem IsUnramifiedOutside.of_algEquiv {K : Type*} [Field K] [Algebra F K] [Algebra k K]
    [IsScalarTower k F K] [Algebra.IsAlgebraic F K] {E' : IntermediateField F K}
    (h : E.IsUnramifiedOutside S) (e : E ≃ₐ[F] E') : E'.IsUnramifiedOutside S where
  finiteDimensional := have := h.finiteDimensional; e.toLinearEquiv.finiteDimensional
  isSeparable := have := h.isSeparable; AlgEquiv.Algebra.isSeparable e
  branchPlaces_subset P hP := h.branchPlaces_subset <| TauCeti.Place.mem_branchPlaces_iff.mpr
    fun hU ↦ TauCeti.Place.mem_branchPlaces_iff.mp hP
      ((TauCeti.Place.isUnramified_iff_of_algEquiv P e).mp hU)

/-- The image of a subextension unramified outside `S` under an embedding over `F` is unramified
outside `S`. -/
theorem IsUnramifiedOutside.map {K : Type*} [Field K] [Algebra F K] [Algebra k K]
    [IsScalarTower k F K] [Algebra.IsAlgebraic F K] (h : E.IsUnramifiedOutside S)
    (f : A →ₐ[F] K) : (E.map f).IsUnramifiedOutside S :=
  h.of_algEquiv (E.equivMap f)

/-- **The trivial extension is unramified outside every set of places.** -/
theorem isUnramifiedOutside_bot (hF : TauCeti.IsFunctionField k F) (S : Set (TauCeti.Place k F)) :
    (⊥ : IntermediateField F A).IsUnramifiedOutside S := by
  -- Inside the trivial Galois extension `F / F`, the bottom field lies in every inertia field.
  have hF' : (⊥ : IntermediateField F F).IsUnramifiedOutside S :=
    .of_isUnramified fun P _ ↦
      (TauCeti.Place.isUnramified_iff_forall_le_inertiaField hF P ⊥).mpr fun _ _ ↦ bot_le
  exact hF'.of_algEquiv ((botEquiv F F).trans (botEquiv F A).symm)

/-- **A compositum of two subextensions unramified outside `S` is unramified outside `S`**
(Stichtenoth, Corollary 3.9.3). -/
theorem IsUnramifiedOutside.sup (hF : TauCeti.IsFunctionField k F)
    (h₁ : E₁.IsUnramifiedOutside S) (h₂ : E₂.IsUnramifiedOutside S) :
    (E₁ ⊔ E₂).IsUnramifiedOutside S := by
  have := h₁.finiteDimensional
  have := h₂.finiteDimensional
  have := h₁.isSeparable
  have := h₂.isSeparable
  exact .of_isUnramified fun P hP ↦
    (TauCeti.Place.isUnramified_sup_iff hF P E₁ E₂).mpr ⟨h₁.isUnramified hP, h₂.isUnramified hP⟩

/-- **A subfield of a subextension unramified outside `S` is unramified outside `S`**: in the
tower `F ⊆ E ⊆ L`, a place of `F` unramified in `L` is unramified in `E`. -/
theorem IsUnramifiedOutside.mono (hF : TauCeti.IsFunctionField k F)
    (h : L.IsUnramifiedOutside S) (hEL : E ≤ L) : E.IsUnramifiedOutside S := by
  have := h.finiteDimensional
  have hL : TauCeti.IsFunctionField k L := hF.finite_extension
  have : FiniteDimensional F E := (restrictAlgEquiv hEL).symm.toLinearEquiv.finiteDimensional
  have : Algebra.IsSeparable F E := (le_separableClosure_iff F A E).mp
    (hEL.trans ((le_separableClosure_iff F A L).mpr h.isSeparable))
  refine .of_isUnramified fun P hP ↦ ?_
  -- View `E` as an intermediate field of `L` and read off the lower step of the tower.
  rw [TauCeti.Place.isUnramified_iff_of_algEquiv P (restrictAlgEquiv hEL)]
  exact ((TauCeti.Place.isUnramified_tower_iff (k₁ := k) (F₁ := restrict hEL) hL P).mp
    (h.isUnramified hP)).left

/-- **A subextension unramified outside `S` is unramified outside every larger set of places.** -/
theorem IsUnramifiedOutside.mono_set {T : Set (TauCeti.Place k F)} (h : E.IsUnramifiedOutside S)
    (hST : S ⊆ T) : E.IsUnramifiedOutside T :=
  ⟨h.finiteDimensional, h.isSeparable, h.branchPlaces_subset.trans hST⟩

end Algebraic

end IntermediateField

namespace TauCeti

section Algebraic

variable [Algebra.IsAlgebraic F A]

variable (A) in
/-- The **maximal subextension of `A / F` unramified outside `S`**: the compositum of all finite
separable subextensions of `A / F` in which every place of `F` outside `S` is unramified. For an
algebraic closure `A` of `k(t)` and the three places `t = 0`, `t = 1` and `t = ∞`, this is the
field `Ω` of the Galois-theoretic fundamental group of the projective line minus three points. -/
def maximalUnramifiedOutside (S : Set (Place k F)) : IntermediateField F A :=
  ⨆ E : {E : IntermediateField F A // E.IsUnramifiedOutside S}, (E : IntermediateField F A)

variable (A) in
/-- The maximal subextension unramified outside `S` is the compositum of the subextensions
unramified outside `S`. -/
theorem maximalUnramifiedOutside_def (S : Set (Place k F)) :
    maximalUnramifiedOutside A S =
      ⨆ E : {E : IntermediateField F A // E.IsUnramifiedOutside S}, (E : IntermediateField F A) :=
  -- `(rfl)`, not `rfl`: keep the body opaque while exporting this equation across modules.
  (rfl)

variable {S : Set (Place k F)} {E : IntermediateField F A}

/-- A subextension unramified outside `S` lies in the maximal one. -/
theorem _root_.IntermediateField.IsUnramifiedOutside.le_maximalUnramifiedOutside
    (h : E.IsUnramifiedOutside S) : E ≤ maximalUnramifiedOutside A S :=
  (maximalUnramifiedOutside_def A S).symm ▸
    le_iSup (fun E : {E : IntermediateField F A // E.IsUnramifiedOutside S} ↦
      (E : IntermediateField F A)) ⟨E, h⟩

/-- **The maximal subextension unramified outside `S` grows with `S`.** -/
@[gcongr]
theorem maximalUnramifiedOutside_mono {T : Set (Place k F)} (hST : S ⊆ T) :
    maximalUnramifiedOutside A S ≤ maximalUnramifiedOutside A T := by
  rw [maximalUnramifiedOutside_def A S]
  exact iSup_le fun E ↦ (E.property.mono_set hST).le_maximalUnramifiedOutside

/-- A finite compositum of subextensions unramified outside `S` is unramified outside `S`. -/
private theorem isUnramifiedOutside_finsetSup (hF : IsFunctionField k F)
    (s : Finset {E : IntermediateField F A // E.IsUnramifiedOutside S}) :
    (⨆ E ∈ s, (E : IntermediateField F A)).IsUnramifiedOutside S := by
  rw [← Finset.sup_eq_iSup]
  exact Finset.sup_induction (p := (IntermediateField.IsUnramifiedOutside · S))
    (isUnramifiedOutside_bot hF S) (fun _ h₁ _ h₂ ↦ h₁.sup hF h₂) fun E _ ↦ E.property

/-- **The finite subextensions of the maximal subextension unramified outside `S` are exactly
the finite subextensions unramified outside `S`.** A finite subextension is finitely generated,
so if it lies in the compositum of the family it lies in a finite compositum of members. -/
theorem le_maximalUnramifiedOutside_iff (hF : IsFunctionField k F) [FiniteDimensional F E] :
    E ≤ maximalUnramifiedOutside A S ↔ E.IsUnramifiedOutside S := by
  refine ⟨fun hE ↦ ?_, IsUnramifiedOutside.le_maximalUnramifiedOutside⟩
  obtain ⟨t, ht, rfl⟩ := fg_def.mp (essFiniteType_iff.mp (inferInstance :
    Algebra.EssFiniteType F E))
  obtain ⟨s, hs⟩ := (adjoin_finite_isCompactElement ht).exists_finset_of_le_iSup _ hE
  exact (isUnramifiedOutside_finsetSup hF s).mono hF hs

/-- An element lies in the maximal subextension unramified outside `S` exactly when the
subextension of `A / F` it generates is unramified outside `S`. -/
theorem mem_maximalUnramifiedOutside_iff (hF : IsFunctionField k F) {x : A} :
    x ∈ maximalUnramifiedOutside A S ↔ F⟮x⟯.IsUnramifiedOutside S := by
  have : FiniteDimensional F F⟮x⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  rw [← adjoin_simple_le_iff, le_maximalUnramifiedOutside_iff hF]

/-- The maximal subextension unramified outside `S` is separable, as a compositum of separable
extensions. -/
instance instIsSeparableMaximalUnramifiedOutside :
    Algebra.IsSeparable F (maximalUnramifiedOutside A S) := by
  have (E : {E : IntermediateField F A // E.IsUnramifiedOutside S}) :
      Algebra.IsSeparable F (E : IntermediateField F A) :=
    E.property.isSeparable
  rw [maximalUnramifiedOutside_def]
  infer_instance

/-- **Every embedding of `A` into itself over `F` maps the maximal subextension unramified
outside `S` into itself**, since it carries each subextension unramified outside `S` to an
isomorphic one. -/
theorem map_maximalUnramifiedOutside_le (σ : A →ₐ[F] A) :
    (maximalUnramifiedOutside A S).map σ ≤ maximalUnramifiedOutside A S := by
  rw [maximalUnramifiedOutside_def, IntermediateField.map_iSup]
  exact iSup_le fun E ↦ (E.property.map σ).le_maximalUnramifiedOutside

end Algebraic

section Normal

variable [Normal F A] {S : Set (Place k F)}

/-- Over a normal extension `A / F`, the maximal subextension unramified outside `S` is normal. -/
instance instNormalMaximalUnramifiedOutside :
    Normal F (maximalUnramifiedOutside A S) :=
  normal_iff_forall_map_le.mpr map_maximalUnramifiedOutside_le

/-- **Over a normal extension `A / F`, the maximal subextension unramified outside `S` is a
Galois extension of `F`.** Its Galois group, with the Krull topology, is a profinite group. -/
instance instIsGaloisMaximalUnramifiedOutside :
    IsGalois F (maximalUnramifiedOutside A S) :=
  ⟨⟩

end Normal

section Algebraic

variable [Algebra.IsAlgebraic F A] {S : Set (Place k F)}

/-- An intermediate field of the maximal subextension unramified outside `S`, regarded as a
subextension of `A`, is unramified outside `S` exactly when it is finite over `F`. -/
theorem isUnramifiedOutside_lift_iff (hF : IsFunctionField k F)
    (E : IntermediateField F (maximalUnramifiedOutside A S)) :
    (lift E).IsUnramifiedOutside S ↔ FiniteDimensional F E := by
  refine ⟨fun h ↦ ?_, fun _ ↦ ?_⟩
  · have := h.finiteDimensional
    exact (liftAlgEquiv E).symm.toLinearEquiv.finiteDimensional
  · have : FiniteDimensional F (lift E) := (liftAlgEquiv E).toLinearEquiv.finiteDimensional
    exact (le_maximalUnramifiedOutside_iff hF).mp (lift_le E)

end Algebraic

variable [Normal F A] {S : Set (Place k F)}

/-- The finite Galois subextension of `A / F` cut out by an open normal subgroup of the Galois
group of the maximal subextension unramified outside `S`: the fixed field of the subgroup,
regarded as a subextension of `A`. -/
private def fixedFieldLift (hF : IsFunctionField k F)
    (U : OpenNormalSubgroup Gal(maximalUnramifiedOutside A S/F)) :
    {L : FiniteGaloisIntermediateField F A // L.toIntermediateField.IsUnramifiedOutside S} :=
  have hU : (fixedField U.toSubgroup).fixingSubgroup = U.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨U.toSubgroup, U.toOpenSubgroup.isClosed⟩
  have h := (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois
    (fixedField U.toSubgroup)).mp ⟨by rw [hU]; exact U.isOpen', by rw [hU]; exact U.isNormal'⟩
  have := h.left
  have := h.right
  have : FiniteDimensional F (lift (fixedField U.toSubgroup)) :=
    (liftAlgEquiv _).toLinearEquiv.finiteDimensional
  have : IsGalois F (lift (fixedField U.toSubgroup)) := IsGalois.of_algEquiv (liftAlgEquiv _)
  ⟨{ toIntermediateField := lift (fixedField U.toSubgroup) },
    (isUnramifiedOutside_lift_iff hF _).mpr h.left⟩

/-- The open normal subgroup of the Galois group of the maximal subextension unramified outside
`S` fixing a finite Galois subextension of `A / F` unramified outside `S`. -/
private def fixingOpenNormalSubgroup
    (E : {L : FiniteGaloisIntermediateField F A // L.toIntermediateField.IsUnramifiedOutside S}) :
    OpenNormalSubgroup Gal(maximalUnramifiedOutside A S/F) :=
  have hE := E.property.le_maximalUnramifiedOutside
  have : FiniteDimensional F (restrict hE) := (restrictAlgEquiv hE).toLinearEquiv.finiteDimensional
  have : IsGalois F (restrict hE) := IsGalois.of_algEquiv (restrictAlgEquiv hE)
  { toSubgroup := (restrict hE).fixingSubgroup
    isOpen' := (restrict hE).fixingSubgroup_isOpen
    isNormal' := ((InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois _).mpr
      ⟨inferInstance, inferInstance⟩).right }

namespace maximalUnramifiedOutside

/-- **The open normal subgroups of the Galois group of the maximal subextension of `A / F`
unramified outside `S` correspond to the finite Galois subextensions of `A / F` unramified outside
`S`**: a subgroup is sent to its fixed field and a subextension to the subgroup fixing it. -/
def openNormalSubgroupEquiv (hF : IsFunctionField k F) :
    OpenNormalSubgroup Gal(maximalUnramifiedOutside A S/F) ≃
      {L : FiniteGaloisIntermediateField F A // L.toIntermediateField.IsUnramifiedOutside S} where
  toFun := fixedFieldLift hF
  invFun := fixingOpenNormalSubgroup
  left_inv U := by
    refine OpenNormalSubgroup.toSubgroup_injective ?_
    -- Unfold the two file-private constructions to the underlying fixed field and subgroup.
    change (restrict (lift_le (fixedField U.toSubgroup))).fixingSubgroup = U.toSubgroup
    rw [lift_injective _ (lift_restrict (lift_le (fixedField U.toSubgroup)))]
    exact InfiniteGalois.fixingSubgroup_fixedField ⟨U.toSubgroup, U.toOpenSubgroup.isClosed⟩
  right_inv E := Subtype.ext <| FiniteGaloisIntermediateField.val_injective <| by
    -- Unfold the two file-private constructions to the underlying fixing subgroup and field.
    change lift (fixedField
      (restrict E.property.le_maximalUnramifiedOutside).fixingSubgroup) = E.val.toIntermediateField
    rw [InfiniteGalois.fixedField_fixingSubgroup, lift_restrict]

@[simp]
theorem coe_openNormalSubgroupEquiv_apply (hF : IsFunctionField k F)
    (U : OpenNormalSubgroup Gal(maximalUnramifiedOutside A S/F)) :
    (openNormalSubgroupEquiv (A := A) (S := S) hF U).val.toIntermediateField =
      lift (fixedField U.toSubgroup) :=
  (rfl)

@[simp]
theorem openNormalSubgroupEquiv_symm_apply_toSubgroup (hF : IsFunctionField k F)
    (E : {L : FiniteGaloisIntermediateField F A // L.toIntermediateField.IsUnramifiedOutside S}) :
    ((openNormalSubgroupEquiv (A := A) (S := S) hF).symm E).toSubgroup =
      (restrict E.property.le_maximalUnramifiedOutside).fixingSubgroup :=
  (rfl)

end maximalUnramifiedOutside

end TauCeti
