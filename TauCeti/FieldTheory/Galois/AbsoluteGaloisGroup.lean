/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!
# The absolute Galois group of a field, taken at its separable closure

For a normal extension `E/F` an automorphism of `E` is determined by, and determined on, the
separable closure of `F` in `E`: restriction

```
Gal(E/F) → Gal(separableClosure F E / F)
```

is an isomorphism of topological groups, `TauCeti.separableClosureRestrictEquiv`. Specialised to
`E = AlgebraicClosure F` this identifies Mathlib's `Field.absoluteGaloisGroup F`, defined through
the algebraic closure, with `TauCeti.AbsoluteGaloisGroup F = Gal(SeparableClosure F / F)`, which is
the carrier every Galois-cohomological statement is written against.

Which of the two closures is used is not a matter of taste.
`TauCeti.mem_perfectClosure_iff_fixed` says
that the elements of a normal `E/F` fixed by every `F`-automorphism are exactly the elements purely
inseparable over `F`. So for an imperfect `F` the fixed field of `Field.absoluteGaloisGroup F` is
the purely inseparable closure of `F` and not `F` itself, while over the separable closure
`InfiniteGalois.mem_range_algebraMap_iff_fixed` gives the fixed field `F` that a Galois descent
argument needs. The two groups are nonetheless the same topological group, which is what makes it
legitimate to state a theorem for one and use it for the other.

Everything Mathlib proves for a Galois extension therefore transports. Compactness does, so
`Gal(E/F)` is profinite for `E/F` merely normal, and so does the fundamental theorem: the closed
subgroups of `Gal(E/F)` are the fixing subgroups, and they correspond to the intermediate fields of
`separableClosure F E / F`. Intermediate fields of `E` outside the separable closure are not seen
by any fixing subgroup, by `IntermediateField.fixingSubgroup_inf_separableClosure`, which is why
the correspondence is indexed by the separable closure.

## Main definitions and results

* `TauCeti.AbsoluteGaloisGroup K`: the automorphisms of a separable closure of `K`.
* `TauCeti.separableClosureRestrictEquiv`: restriction to the separable closure is an isomorphism
  of topological groups, for any normal extension.
* `TauCeti.absoluteGaloisGroupRestrictEquiv`: its specialisation comparing
  `Field.absoluteGaloisGroup K` with `TauCeti.AbsoluteGaloisGroup K`.
* `IntermediateField.fixingSubgroup_inf_separableClosure`: a fixing subgroup only sees the
  separable part of the intermediate field it fixes.
* `IntermediateField.isClosed_fixingSubgroup`: every fixing subgroup of a normal extension is
  closed.
* `TauCeti.fixingSubgroup_fixedField`: every closed subgroup is a fixing subgroup.
* `TauCeti.intermediateFieldEquivClosedSubgroup`: the fundamental theorem of Galois theory for a
  normal extension.
* `TauCeti.mem_perfectClosure_iff_fixed`: the fixed field of `Gal(E/F)` for a normal
  extension `E/F` is the relative perfect closure of `F` in `E`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. VI §1, for the
  convention that the absolute Galois group of a field is taken at its separable closure.
-/

public section

noncomputable section

namespace TauCeti

variable (F E : Type*) [Field F] [Field E] [Algebra F E]

section Auxiliary

variable {F E}

/-- The preimage of a finite intermediate field `M` of `E/F` under an `F`-algebra map `g` into `E`
is finite over `F`: it is `F`-isomorphic to its image under `g`, which is contained in `M`. -/
private theorem finiteDimensional_comap {L : Type*} [Field L] [Algebra F L] (g : L →ₐ[F] E)
    (M : IntermediateField F E) [FiniteDimensional F M] : FiniteDimensional F (M.comap g) :=
  have hle : (M.comap g).map g ≤ M := (IntermediateField.map_comap_eq g M).le.trans inf_le_left
  Module.Finite.of_injective
    (((IntermediateField.inclusion hle).comp
      (IntermediateField.equivMap (M.comap g) g).toAlgHom).toLinearMap)
    ((IntermediateField.inclusion_injective hle).comp
      (IntermediateField.equivMap (M.comap g) g).injective)

end Auxiliary

section FixingSubgroup

variable {F E}

/-- **A fixing subgroup sees only the separable closure.** For an algebraic extension `E/F` an
`F`-automorphism of `E` fixing `M ⊓ separableClosure F E` pointwise already fixes the intermediate
field `M` pointwise, because every `x ∈ M` has a power `x ^ q ^ n` in that intersection, `q` the
exponential characteristic of `F`. -/
theorem _root_.IntermediateField.fixingSubgroup_inf_separableClosure [Algebra.IsAlgebraic F E]
    (M : IntermediateField F E) :
    (M ⊓ separableClosure F E).fixingSubgroup = M.fixingSubgroup := by
  have hE : ExpChar E (ringExpChar F) :=
    expChar_of_injective_algebraMap (algebraMap F E).injective _
  have hS : ExpChar (separableClosure F E) (ringExpChar F) :=
    expChar_of_injective_algebraMap (algebraMap F (separableClosure F E)).injective _
  refine le_antisymm (fun σ hσ ↦ ?_) (IntermediateField.fixingSubgroup_antitone inf_le_left)
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  intro x hx
  obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem (separableClosure F E) (ringExpChar F) x
  have hyS : x ^ ringExpChar F ^ n ∈ separableClosure F E := by rw [← hy]; exact y.2
  have hpow : σ x ^ ringExpChar F ^ n = x ^ ringExpChar F ^ n := by
    rw [← map_pow]
    exact hσ _ (IntermediateField.mem_inf.mpr ⟨pow_mem hx _, hyS⟩)
  exact iterateFrobenius_inj E (ringExpChar F) n hpow

end FixingSubgroup

section Normal

variable [Normal F E]

/-! ### Restriction to the separable closure -/

namespace AlgEquiv

/-- An `F`-automorphism of a normal extension `E/F` that is the identity on the separable closure
of `F` in `E` is the identity: what is left of the extension is purely inseparable. -/
theorem restrictNormalHom_separableClosure_injective :
    Function.Injective
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (separableClosure F E)) := by
  rw [← MonoidHom.ker_eq_bot_iff, IntermediateField.restrictNormalHom_ker]
  have h : Subsingleton Gal(E/(separableClosure F E)) :=
    AlgEquiv.coe_toAlgHom_injective.subsingleton
  have h' : Subsingleton (separableClosure F E).fixingSubgroup :=
    (IntermediateField.fixingSubgroupEquiv _).toEquiv.subsingleton
  exact Subgroup.eq_bot_of_subsingleton _

end AlgEquiv

variable {F E}

/-- A homomorphism into `Gal(E/F)` lifting the automorphisms of the separable closure is
continuous.

This is the criterion the inverse of `separableClosureRestrictEquiv` is checked against, and it is
where the topologies are compared: the fixing subgroup of a finite subextension `M` of `E` is
pulled back to the fixing subgroup of `M ∩ separableClosure F E`, which by
`IntermediateField.fixingSubgroup_inf_separableClosure` cuts out the same automorphisms of `E`
as `M` does. -/
private theorem continuous_of_algebraMap_comm (s : Gal(separableClosure F E/F) → Gal(E/F))
    (hmul : ∀ a b, s (a * b) = s a * s b)
    (hs : ∀ (τ : Gal(separableClosure F E/F)) (y : separableClosure F E),
      s τ (algebraMap (separableClosure F E) E y) =
        algebraMap (separableClosure F E) E (τ y)) :
    Continuous s := by
  refine continuous_of_continuousAt_one (MonoidHom.mk' s hmul)
    (continuousAt_def.mpr fun N hN ↦ ?_)
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨M, hM, hMN⟩ := hN
  have : FiniteDimensional F M := hM
  rw [krullTopology_mem_nhds_one_iff]
  -- `M.comap g` is `M ∩ separableClosure F E`.
  set g : separableClosure F E →ₐ[F] E := IsScalarTower.toAlgHom F _ E
  refine ⟨M.comap g, finiteDimensional_comap g M, fun τ hτ ↦ hMN ?_⟩
  -- It is enough that `s τ` fix that intersection, on which it acts through `τ`.
  rw [SetLike.mem_coe, ← IntermediateField.fixingSubgroup_inf_separableClosure M,
    IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  obtain ⟨hxM, hxS⟩ := IntermediateField.mem_inf.mp hx
  have hτx : τ ⟨x, hxS⟩ = ⟨x, hxS⟩ :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ ⟨x, hxS⟩ hxM
  simpa [hτx] using hs τ ⟨x, hxS⟩

variable (F E)

/-- Restriction to the separable closure as a group isomorphism, for a normal extension `E/F`.

This is the underlying multiplicative equivalence of `separableClosureRestrictEquiv`, named so
that the structure field and the inverse-continuity proof below refer to one and the same term
rather than to two separately built copies identified by definitional unfolding. -/
private def separableClosureRestrictMulEquiv : Gal(E/F) ≃* Gal(separableClosure F E/F) :=
  MulEquiv.ofBijective (AlgEquiv.restrictNormalHom (separableClosure F E))
    ⟨AlgEquiv.restrictNormalHom_separableClosure_injective F E,
      AlgEquiv.restrictNormalHom_surjective E⟩

/-- **Restriction to the separable closure is an isomorphism of topological groups**
`Gal(E/F) ≃ₜ* Gal(separableClosure F E / F)`, for a normal extension `E/F`. -/
def separableClosureRestrictEquiv : Gal(E/F) ≃ₜ* Gal(separableClosure F E/F) where
  __ := separableClosureRestrictMulEquiv F E
  continuous_toFun := InfiniteGalois.restrictNormalHom_continuous _
  continuous_invFun :=
    continuous_of_algebraMap_comm (separableClosureRestrictMulEquiv F E).symm
      (map_mul _) fun τ y ↦ by
        conv_rhs => rw [← (separableClosureRestrictMulEquiv F E).apply_symm_apply τ]
        exact (AlgEquiv.restrictNormal_commutes _ _ y).symm

variable {F E}

/-- The isomorphism `separableClosureRestrictEquiv` is the restriction map
`AlgEquiv.restrictNormalHom`, which is what identifies it with the map Mathlib's API is about. -/
theorem separableClosureRestrictEquiv_apply (σ : Gal(E/F)) :
    separableClosureRestrictEquiv F E σ = AlgEquiv.restrictNormalHom (separableClosure F E) σ :=
  (rfl)

/-- Restricting `σ : Gal(E/F)` to the separable closure does not move elements: the image of
`x ∈ separableClosure F E` under `separableClosureRestrictEquiv F E σ` is `σ x`, computed in `E`. -/
@[simp]
theorem coe_separableClosureRestrictEquiv_apply (σ : Gal(E/F)) (x : separableClosure F E) :
    (separableClosureRestrictEquiv F E σ x : E) = σ x :=
  AlgEquiv.restrictNormal_commutes _ _ x

/-- The automorphism of `E` extending `τ : Gal(separableClosure F E/F)` agrees with `τ` on the
separable closure. -/
@[simp]
theorem separableClosureRestrictEquiv_symm_apply_coe (τ : Gal(separableClosure F E/F))
    (x : separableClosure F E) :
    (separableClosureRestrictEquiv F E).symm τ (x : E) = (τ x : E) := by
  conv_rhs => rw [← (separableClosureRestrictEquiv F E).apply_symm_apply τ]
  exact (coe_separableClosureRestrictEquiv_apply _ x).symm

/-! ### The profinite structure -/

variable (F E)

/-- **The Galois group of a normal extension is compact**, hence, the Krull topology being
totally separated, a profinite group: `ProfiniteGrp.of Gal(E/F)`. Mathlib has compactness for a
Galois extension, and restriction to the separable closure carries it over. -/
instance : CompactSpace Gal(E/F) :=
  (separableClosureRestrictEquiv F E).toHomeomorph.symm.compactSpace

variable {F E}

/-! ### The Galois correspondence -/

/-- `IntermediateField.map_fixingSubgroup` for the separable closure, phrased with
`IntermediateField.lift`. The two sides are definitionally equal — `lift M` is `M.map (val _)` —
but `rw` does not see through `IntermediateField.lift`, so the rewrites below need this form. -/
private theorem fixingSubgroup_lift (M : IntermediateField F (separableClosure F E)) :
    (IntermediateField.lift M).fixingSubgroup =
      M.fixingSubgroup.comap (AlgEquiv.restrictNormalHom (separableClosure F E)) :=
  IntermediateField.map_fixingSubgroup (E' := E) M

/-- **The fixing subgroup of an intermediate field of a normal extension is closed.** This is
`InfiniteGalois.fixingSubgroup_isClosed` with the separability hypothesis on `E/F` removed: the
fixing subgroup of `L` is the preimage, under restriction to the separable closure, of the fixing
subgroup of the part of `L` lying there. -/
theorem _root_.IntermediateField.isClosed_fixingSubgroup (L : IntermediateField F E) :
    IsClosed (L.fixingSubgroup : Set Gal(E/F)) := by
  rw [← IntermediateField.fixingSubgroup_inf_separableClosure L,
    ← IntermediateField.lift_restrict
      (inf_le_right : L ⊓ separableClosure F E ≤ separableClosure F E),
    fixingSubgroup_lift, Subgroup.coe_comap]
  exact (InfiniteGalois.fixingSubgroup_isClosed _).preimage
    (InfiniteGalois.restrictNormalHom_continuous _)

/-- **An intermediate field of the separable closure is the part of the fixed field of its fixing
subgroup that lies in the separable closure.** Over an imperfect `F` the fixed field itself is
larger: it is the relative perfect closure, by `mem_perfectClosure_iff_fixed`. -/
theorem fixedField_fixingSubgroup_lift_inf_separableClosure
    (M : IntermediateField F (separableClosure F E)) :
    IntermediateField.fixedField (IntermediateField.lift M).fixingSubgroup ⊓
        separableClosure F E = IntermediateField.lift M := by
  rw [InfiniteGalois.restrict_fixedField, fixingSubgroup_lift,
    Subgroup.map_comap_eq_self_of_surjective (AlgEquiv.restrictNormalHom_surjective E),
    InfiniteGalois.fixedField_fixingSubgroup]

/-- **A closed subgroup of `Gal(E/F)` is the fixing subgroup of its fixed field**, for `E/F`
normal. -/
theorem fixingSubgroup_fixedField {H : Subgroup Gal(E/F)}
    (hH : IsClosed (H : Set Gal(E/F))) :
    (IntermediateField.fixedField H).fixingSubgroup = H := by
  have hmap : IsClosed ((H.map (AlgEquiv.restrictNormalHom (separableClosure F E)) :
      Subgroup Gal(separableClosure F E/F)) : Set Gal(separableClosure F E/F)) := by
    rw [Subgroup.coe_map]
    exact (separableClosureRestrictEquiv F E).toHomeomorph.isClosedMap _ hH
  rw [← IntermediateField.fixingSubgroup_inf_separableClosure,
    InfiniteGalois.restrict_fixedField, fixingSubgroup_lift,
    InfiniteGalois.fixingSubgroup_fixedField ⟨_, hmap⟩,
    Subgroup.comap_map_eq_self_of_injective
      (AlgEquiv.restrictNormalHom_separableClosure_injective F E)]

/-- **The fundamental theorem of Galois theory in the ambient model.** For a normal extension
`E/F` the closed subgroups of `Gal(E/F)` correspond, inclusion-reversingly, to the intermediate
fields of the separable closure `separableClosure F E / F`; an intermediate field of `E` outside
the separable closure has the same fixing subgroup as its separable part. -/
def intermediateFieldEquivClosedSubgroup :
    IntermediateField F (separableClosure F E) ≃o (ClosedSubgroup Gal(E/F))ᵒᵈ where
  toFun M := ⟨(IntermediateField.lift M).fixingSubgroup,
    IntermediateField.isClosed_fixingSubgroup _⟩
  invFun H := IntermediateField.restrict
    (inf_le_right : IntermediateField.fixedField H.1 ⊓ _ ≤ separableClosure F E)
  left_inv M := IntermediateField.lift_injective _ <| by
    rw [IntermediateField.lift_restrict, fixedField_fixingSubgroup_lift_inf_separableClosure]
  right_inv H := by
    apply ClosedSubgroup.toSubgroup_injective
    dsimp only
    rw [IntermediateField.lift_restrict, IntermediateField.fixingSubgroup_inf_separableClosure,
      fixingSubgroup_fixedField H.isClosed']
  map_rel_iff' {M₁ M₂} := by
    refine ⟨fun h ↦ ?_, fun h ↦ IntermediateField.fixingSubgroup_le
      ((IntermediateField.gc_map_comap _).monotone_l h)⟩
    have h₁ : IntermediateField.lift M₁ ≤ IntermediateField.lift M₂ := by
      rw [← fixedField_fixingSubgroup_lift_inf_separableClosure M₂]
      exact le_inf ((IntermediateField.le_iff_le _ _).mpr h) (IntermediateField.lift_le M₁)
    exact fun y hy ↦ (IntermediateField.mem_lift y).mp (h₁ ((IntermediateField.mem_lift y).mpr hy))

/-- The correspondence sends an intermediate field to the fixing subgroup of its lift. -/
theorem intermediateFieldEquivClosedSubgroup_apply
    (M : IntermediateField F (separableClosure F E)) :
    (OrderDual.ofDual (intermediateFieldEquivClosedSubgroup (F := F) (E := E) M)).toSubgroup =
      (IntermediateField.lift M).fixingSubgroup :=
  (rfl)

/-- The inverse of the correspondence sends a closed subgroup to the part of its fixed field that
lies in the separable closure. -/
theorem lift_intermediateFieldEquivClosedSubgroup_symm_apply (H : ClosedSubgroup Gal(E/F)) :
    IntermediateField.lift ((intermediateFieldEquivClosedSubgroup (F := F) (E := E)).symm H) =
      IntermediateField.fixedField H.1 ⊓ separableClosure F E :=
  IntermediateField.lift_restrict _

/-! ### The fixed field of a normal extension -/

/-- **The fixed field of `Gal(E/F)` for a normal extension `E/F` is the relative perfect closure**
of `F` in `E`, and not `F`. The two agree exactly when `E/F` has no nontrivial purely inseparable
part, so for `E` an algebraic closure they agree exactly when `F` is perfect. -/
theorem mem_perfectClosure_iff_fixed {x : E} :
    x ∈ perfectClosure F E ↔ ∀ σ : Gal(E/F), σ x = x := by
  have hSq : ExpChar (separableClosure F E) (ringExpChar F) :=
    expChar_of_injective_algebraMap (algebraMap F (separableClosure F E)).injective _
  refine ⟨fun hx σ ↦ ?_, fun hx ↦ ?_⟩
  · -- `perfectClosure F E` is purely inseparable over `F`, so `σ` and the inclusion are the same
    -- `F`-algebra map on it.
    exact AlgHom.congr_fun
      (Subsingleton.elim (σ.toAlgHom.comp (perfectClosure F E).val) (perfectClosure F E).val)
      ⟨x, hx⟩
  · -- Push `x` into the separable closure by a `q`-th power, where the fixed field is `F`.
    obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem (separableClosure F E) (ringExpChar F) x
    have hfix : ∀ τ : Gal(separableClosure F E/F), τ y = y := fun τ ↦ by
      have h2 : (separableClosureRestrictEquiv F E).symm τ
          (algebraMap (separableClosure F E) E y) = algebraMap (separableClosure F E) E y := by
        rw [hy, map_pow, hx]
      rw [IntermediateField.algebraMap_apply, separableClosureRestrictEquiv_symm_apply_coe] at h2
      exact Subtype.ext h2
    obtain ⟨b, hb⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed y).mpr hfix
    exact (mem_perfectClosure_iff_pow_mem (F := F) (E := E) (ringExpChar F)).mpr
      ⟨n, b, by rw [IsScalarTower.algebraMap_apply F (separableClosure F E) E, hb, hy]⟩

end Normal

/-! ### The absolute Galois group -/

variable (K : Type*) [Field K]

/-- The absolute Galois group of `K`: the group of automorphisms of a separable closure of `K`.

This, rather than Mathlib's `Field.absoluteGaloisGroup`, is the group Galois cohomology is stated
at, because it is `Kˢ` and not an algebraic closure whose invariants are `K` for every `K`. It is
an abbreviation so that the Krull topology, the profinite structure and the action on `Kˢ` are the
ones Mathlib already provides for `Gal(E/F)`; `absoluteGaloisGroupRestrictEquiv` compares it with
`Field.absoluteGaloisGroup`. -/
abbrev AbsoluteGaloisGroup := Gal(SeparableClosure K/K)

/-- **Mathlib's absolute Galois group and `AbsoluteGaloisGroup` are the same topological group**:
restricting an automorphism of an algebraic closure of `K` to the separable closure is an
isomorphism `Field.absoluteGaloisGroup K ≃ₜ* AbsoluteGaloisGroup K`.

Its forward map is restriction, `absoluteGaloisGroupRestrictEquiv_apply`, and both directions are
computed on elements of `SeparableClosure K` by `coe_absoluteGaloisGroupRestrictEquiv_apply` and
`absoluteGaloisGroupRestrictEquiv_symm_apply_coe`. Those lemmas are stated on applications rather
than on the isomorphisms themselves, because `Field.absoluteGaloisGroup K` carries its own derived
group and topology instances, so an equation between the isomorphisms is not usable by `rw`. -/
def absoluteGaloisGroupRestrictEquiv :
    Field.absoluteGaloisGroup K ≃ₜ* AbsoluteGaloisGroup K :=
  separableClosureRestrictEquiv K (AlgebraicClosure K)

/-- The comparison isomorphism is the restriction map `AlgEquiv.restrictNormalHom`, which is what
identifies it with the map Mathlib's API is about. -/
theorem absoluteGaloisGroupRestrictEquiv_apply (σ : Gal(AlgebraicClosure K/K)) :
    absoluteGaloisGroupRestrictEquiv K σ =
      AlgEquiv.restrictNormalHom (separableClosure K (AlgebraicClosure K)) σ :=
  (rfl)

/-- An automorphism of an algebraic closure of `K` and its image in `AbsoluteGaloisGroup K` take
the same value on an element of `SeparableClosure K`, computed in the algebraic closure. -/
@[simp]
theorem coe_absoluteGaloisGroupRestrictEquiv_apply (σ : Gal(AlgebraicClosure K/K))
    (x : SeparableClosure K) :
    (absoluteGaloisGroupRestrictEquiv K σ x : AlgebraicClosure K) = σ x :=
  coe_separableClosureRestrictEquiv_apply _ x

/-- The automorphism of `AlgebraicClosure K` extending `τ : AbsoluteGaloisGroup K` agrees with `τ`
on `SeparableClosure K`; this is what computes the inverse of the comparison isomorphism.

The coercion to a function carries its type argument explicitly because
`Field.absoluteGaloisGroup K` is a plain definition, so elaboration does not see an element of it
as a function on `AlgebraicClosure K` on its own. -/
@[simp]
theorem absoluteGaloisGroupRestrictEquiv_symm_apply_coe (τ : AbsoluteGaloisGroup K)
    (x : SeparableClosure K) :
    DFunLike.coe (F := Gal(AlgebraicClosure K/K)) ((absoluteGaloisGroupRestrictEquiv K).symm τ)
        (x : AlgebraicClosure K) = (τ x : AlgebraicClosure K) :=
  separableClosureRestrictEquiv_symm_apply_coe _ x

/-- `Field.absoluteGaloisGroup K` is compact. It is a type of its own rather than a notation for
`Gal(AlgebraicClosure K/K)`, so the instance has to be transported by hand. -/
instance : CompactSpace (Field.absoluteGaloisGroup K) :=
  inferInstanceAs (CompactSpace Gal(AlgebraicClosure K/K))

/-- `Field.absoluteGaloisGroup K` is totally separated, hence totally disconnected and Hausdorff.
With compactness this makes it a profinite group, `ProfiniteGrp.of (Field.absoluteGaloisGroup K)`.
-/
instance : TotallySeparatedSpace (Field.absoluteGaloisGroup K) :=
  inferInstanceAs (TotallySeparatedSpace Gal(AlgebraicClosure K/K))

-- the two instances above are what make the profinite group object available
example : ProfiniteGrp := ProfiniteGrp.of (Field.absoluteGaloisGroup K)

/-- The absolute Galois group of a separably closed field is trivial. -/
instance [IsSepClosed K] : Subsingleton (AbsoluteGaloisGroup K) := by
  have hbot : separableClosure K (AlgebraicClosure K) = ⊥ :=
    (IsSepClosed.separableClosure_eq_bot_iff K (AlgebraicClosure K)).mpr ‹_›
  refine ⟨fun σ τ ↦ AlgEquiv.ext fun x ↦ ?_⟩
  have hxb : (x : AlgebraicClosure K) ∈ (⊥ : IntermediateField K (AlgebraicClosure K)) := by
    rw [← hbot]; exact x.2
  obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp hxb
  have hx : x = algebraMap K _ y := Subtype.ext hy.symm
  rw [hx, AlgEquiv.commutes, AlgEquiv.commutes]

end TauCeti
