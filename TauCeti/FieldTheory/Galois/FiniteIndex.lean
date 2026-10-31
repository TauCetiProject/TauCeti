/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.Relrank
public import TauCeti.FieldTheory.Galois.FixedField

/-!
# Fixed fields of subgroups of finite index

Let `U` be a group of automorphisms of a field extension `M / K`, of any cardinality, and let
`x : M`. Over the fixed field `M^U`, the element `x` is integral exactly when its `U`-orbit is
finite. Its minimal polynomial is then the product of `X - y` over that orbit, so it is
separable, its roots are the orbit, and its degree is the index of the stabilizer of `x` in `U`.
This is Artin's description of the minimal polynomial over the fixed field of a finite group,
with finiteness of the group replaced by finiteness of a single orbit.

For subgroups `V ≤ U` with `[U : V]` finite, every element of `M^V` has stabilizer containing
`V`, so its degree over `M^U` divides `[U : V]`. By the primitive element theorem `M^V / M^U` is
then a finite separable extension whose degree divides `[U : V]`. The degree equals `[U : V]`
when `V` is closed, meaning that `V` is the full group of automorphisms fixing `M^V`; this case
needs no finiteness hypothesis, an infinite index giving an infinite extension.

No normality of `V` and no topology on `U` is assumed. The results therefore apply to subgroups of
the abstract group `Aut(ℂ)`, whose finite-index subgroups need not be closed. This is how fields
of moduli are shown to be finite over `ℚ`: the stabilizer of an object in a finite orbit of
`Aut(ℂ)` has finite index, and its fixed field is then a finite extension of `ℚ`.

## Main results

* `IntermediateField.isIntegral_fixedField_iff_finite_orbit`: `x` is integral over `M^U` exactly
  when its `U`-orbit is finite.
* `IntermediateField.map_minpoly_fixedField_eq_prod_orbit`: the minimal polynomial of `x` over
  `M^U` is the product of `X - y` over the orbit of `x`.
* `IntermediateField.orbit_eq_rootSet_minpoly_fixedField`: the orbit is the root set of the
  minimal polynomial.
* `IntermediateField.natDegree_minpoly_fixedField_eq_index_stabilizer`: the degree of `x` over
  `M^U` is the index of its stabilizer in `U`.
* `IntermediateField.isSeparable_fixedField_of_isIntegral`: every element integral over `M^U` is
  separable over it.
* `IntermediateField.isSeparable_extendScalars_fixedField`: for `V ≤ U`, an integral
  `M^V / M^U` is separable.
* `IntermediateField.finiteDimensional_fixedField_of_relIndex_ne_zero` and
  `IntermediateField.isSeparable_fixedField_of_relIndex_ne_zero`: for `V ≤ U` of finite index,
  `M^V / M^U` is finite and separable.
* `IntermediateField.relfinrank_fixedField_dvd_relIndex` and
  `IntermediateField.relfinrank_fixedField_le_relIndex`: its degree divides, and is at most,
  `[U : V]`.
* `IntermediateField.relfinrank_fixedField_eq_relIndex`: for closed `V ≤ U`, the degree is
  `[U : V]`.

## References

* [S. Lang, *Algebra*][serge_lang_algebra], Chapter VI, §1, Theorem 1.8 (Artin's theorem), whose
  proof bounds degrees by orbit polynomials and concludes with a primitive element.
* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), (1.6) Lemma,
  for subgroups of finite index in `Aut(ℂ)`.
* The minimal-polynomial argument follows the shape of
  `TauCeti.FiniteField.map_minpoly_eq_prod_orbit` in `TauCeti/FieldTheory/Finite/MinpolyOrbit.lean`,
  which treats the Frobenius orbit over a finite base field.
-/

public section

open Polynomial MulAction

namespace IntermediateField

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

section Orbit

variable (U : Subgroup (M ≃ₐ[K] M))

-- Every element of `U` fixes the fixed field of `U`.
private theorem mem_fixingSubgroup_fixedField (u : U) :
    (u : M ≃ₐ[K] M) ∈ (fixedField U).fixingSubgroup :=
  (le_fixedField_iff_le_fixingSubgroup _ _).mp le_rfl u.2

-- The elements of `U` permute the roots of a polynomial with coefficients in `fixedField U`.
private theorem aeval_smul_eq_zero {p : (fixedField U)[X]} {x : M} (hp : aeval x p = 0) (u : U) :
    aeval (u • x) p = 0 := by
  have h := aeval_algHom_apply
    (fixingSubgroupEquiv (fixedField U) ⟨u, mem_fixingSubgroup_fixedField U u⟩).toAlgHom x p
  simpa [hp, Subgroup.smul_def, AlgEquiv.smul_def] using h

variable {U} {x : M}

private theorem orbit_subset_rootSet_minpoly (hx : IsIntegral (fixedField U) x) :
    orbit U x ⊆ (minpoly (fixedField U) x).rootSet M := by
  rintro _ ⟨u, rfl⟩
  exact mem_rootSet.mpr ⟨minpoly.ne_zero hx, aeval_smul_eq_zero U (minpoly.aeval _ x) u⟩

-- The product of `X - y` over a finite `U`-orbit is fixed by `U`, so it has a monic lift to
-- `fixedField U` of the same degree.
private theorem exists_monic_map_eq_prod_orbit (hx : (orbit U x).Finite) :
    ∃ q : (fixedField U)[X], q.map (algebraMap (fixedField U) M) = ∏ y ∈ hx.toFinset, (X - C y) ∧
      q.Monic := by
  classical
  set s := hx.toFinset
  have hs : ∀ y, y ∈ s ↔ y ∈ orbit U x := fun y ↦ Set.Finite.mem_toFinset hx
  have hinv : ∀ u : U, u • ∏ y ∈ s, (X - C y) = ∏ y ∈ s, (X - C y) := fun u ↦ by
    rw [Finset.smul_prod']
    simp_rw [smul_sub, smul_X, smul_C]
    refine Finset.prod_nbij' (u • ·) (u⁻¹ • ·) (fun y hy ↦ ?_) (fun y hy ↦ ?_)
      (fun y _ ↦ inv_smul_smul u y) (fun y _ ↦ smul_inv_smul u y) fun y _ ↦ rfl
    · exact (hs _).mpr (mem_orbit_of_mem_orbit u ((hs y).mp hy))
    · exact (hs _).mpr (mem_orbit_of_mem_orbit u⁻¹ ((hs y).mp hy))
  have hlifts : ∏ y ∈ s, (X - C y) ∈ lifts (algebraMap (fixedField U) M) := by
    refine (lifts_iff_coeff_lifts _).mpr fun n ↦
      ⟨⟨(∏ y ∈ s, (X - C y)).coeff n, (mem_fixedField_iff _ _).mpr fun u hu ↦ ?_⟩, rfl⟩
    simpa [coeff_smul] using congrArg (fun p : M[X] ↦ p.coeff n) (hinv ⟨u, hu⟩)
  obtain ⟨q, hq, -, hmonic⟩ := lifts_and_natDegree_eq_and_monic hlifts
    (monic_prod_of_monic _ _ fun y _ ↦ monic_X_sub_C y)
  exact ⟨q, hq, hmonic⟩

/-- **An element with a finite orbit is integral over the fixed field**: it is a root of the
product of `X - y` over its orbit, whose coefficients are fixed by `U`. -/
theorem isIntegral_fixedField_of_finite_orbit (hx : (orbit U x).Finite) :
    IsIntegral (fixedField U) x := by
  classical
  obtain ⟨q, hq, hmonic⟩ := exists_monic_map_eq_prod_orbit hx
  refine ⟨q, hmonic, ?_⟩
  rw [← eval_map, hq, eval_prod]
  exact Finset.prod_eq_zero (hx.mem_toFinset.mpr (mem_orbit_self x)) (by simp)

/-- An element integral over the fixed field of `U` has a finite `U`-orbit, contained in the roots
of its minimal polynomial. -/
theorem finite_orbit_of_isIntegral_fixedField (hx : IsIntegral (fixedField U) x) :
    (orbit U x).Finite :=
  ((minpoly (fixedField U) x).rootSet M).toFinite.subset (orbit_subset_rootSet_minpoly hx)

/-- **An element is integral over the fixed field of a group of automorphisms exactly when its
orbit is finite.** -/
theorem isIntegral_fixedField_iff_finite_orbit :
    IsIntegral (fixedField U) x ↔ (orbit U x).Finite :=
  ⟨finite_orbit_of_isIntegral_fixedField, isIntegral_fixedField_of_finite_orbit⟩

/-- **Artin's minimal polynomial for a finite orbit**: over the fixed field of a group `U` of
automorphisms, the minimal polynomial of an element with finite `U`-orbit is, read in `M[X]`,
the product of `X - y` over that orbit. -/
theorem map_minpoly_fixedField_eq_prod_orbit (hx : (orbit U x).Finite) :
    (minpoly (fixedField U) x).map (algebraMap (fixedField U) M) =
      ∏ y ∈ hx.toFinset, (X - C y) := by
  classical
  obtain ⟨q, hq, hqmonic⟩ := exists_monic_map_eq_prod_orbit hx
  have hint := isIntegral_fixedField_of_finite_orbit hx
  have hmonic : ((minpoly (fixedField U) x).map (algebraMap (fixedField U) M)).Monic :=
    (minpoly.monic hint).map _
  -- the minimal polynomial divides the lift of the orbit product
  have hqx : aeval x q = 0 := by
    rw [aeval_def, ← eval_map, hq, eval_prod]
    exact Finset.prod_eq_zero (hx.mem_toFinset.mpr (mem_orbit_self x)) (by simp)
  have h₁ : (minpoly (fixedField U) x).map (algebraMap (fixedField U) M) ∣
      ∏ y ∈ hx.toFinset, (X - C y) :=
    hq ▸ Polynomial.map_dvd _ (minpoly.dvd _ x hqx)
  -- and each element of the orbit is a simple factor of the minimal polynomial
  have h₂ : ∏ y ∈ hx.toFinset, (X - C y) ∣
      (minpoly (fixedField U) x).map (algebraMap (fixedField U) M) := by
    rw [Finset.prod_eq_multiset_prod, Multiset.prod_X_sub_C_dvd_iff_le_roots hmonic.ne_zero,
      Finset.val_le_iff_val_subset]
    intro y hy
    rw [mem_roots hmonic.ne_zero, IsRoot.def, eval_map, ← aeval_def]
    exact (mem_rootSet.mp (orbit_subset_rootSet_minpoly hint (hx.mem_toFinset.mp hy))).2
  exact eq_of_monic_of_associated hmonic (monic_prod_of_monic _ _ fun y _ ↦ monic_X_sub_C y)
    (associated_of_dvd_dvd h₁ h₂)

/-- **The orbit of an integral element is the root set of its minimal polynomial** over the fixed
field. -/
theorem orbit_eq_rootSet_minpoly_fixedField (hx : IsIntegral (fixedField U) x) :
    orbit U x = (minpoly (fixedField U) x).rootSet M := by
  classical
  have hfin := finite_orbit_of_isIntegral_fixedField hx
  refine (orbit_subset_rootSet_minpoly hx).antisymm fun y hy ↦ ?_
  have h := (mem_rootSet.mp hy).2
  rw [aeval_def, ← eval_map, map_minpoly_fixedField_eq_prod_orbit hfin, eval_prod,
    Finset.prod_eq_zero_iff] at h
  obtain ⟨z, hz, hyz⟩ := h
  rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hyz
  exact hyz ▸ hfin.mem_toFinset.mp hz

variable (U x) in
/-- **The degree over the fixed field is the index of the stabilizer.** When the orbit is
infinite both sides are `0`: the element is then not integral over the fixed field. -/
theorem natDegree_minpoly_fixedField_eq_index_stabilizer :
    (minpoly (fixedField U) x).natDegree = (stabilizer U x).index := by
  classical
  rw [index_stabilizer]
  by_cases hx : (orbit U x).Finite
  · rw [← natDegree_map (algebraMap (fixedField U) M), map_minpoly_fixedField_eq_prod_orbit hx,
      natDegree_prod _ _ fun y _ ↦ X_sub_C_ne_zero y, Set.ncard_eq_toFinset_card _ hx]
    simp
  · rw [minpoly.eq_zero (mt finite_orbit_of_isIntegral_fixedField hx), natDegree_zero,
      Set.Infinite.ncard hx]

/-- **Elements integral over a fixed field are separable over it**, whatever the
characteristic: the minimal polynomial is a product of distinct linear factors. -/
theorem isSeparable_fixedField_of_isIntegral (hx : IsIntegral (fixedField U) x) :
    IsSeparable (fixedField U) x := by
  classical
  have hfin := finite_orbit_of_isIntegral_fixedField hx
  rw [IsSeparable, ← separable_map (algebraMap (fixedField U) M),
    map_minpoly_fixedField_eq_prod_orbit hfin]
  exact separable_prod_X_sub_C_iff'.mpr fun _ _ _ _ h ↦ h

end Orbit

section FiniteIndex

variable {U V : Subgroup (M ≃ₐ[K] M)}

-- The stabilizer in `U` of an element of `M^V` contains `V ∩ U`.
private theorem subgroupOf_le_stabilizer {y : M} (hy : y ∈ fixedField V) :
    V.subgroupOf U ≤ stabilizer U y := fun u hu ↦ by
  rw [mem_stabilizer_iff, Subgroup.smul_def, AlgEquiv.smul_def]
  exact (mem_fixedField_iff V y).mp hy u (Subgroup.mem_subgroupOf.mp hu)

/-- **The degree of an element of `M^V` over `M^U` divides `[U : V]`**, since its stabilizer in
`U` contains `V ∩ U`. -/
theorem natDegree_minpoly_fixedField_dvd_relIndex {y : M} (hy : y ∈ fixedField V) :
    (minpoly (fixedField U) y).natDegree ∣ V.relIndex U := by
  rw [natDegree_minpoly_fixedField_eq_index_stabilizer]
  exact Subgroup.index_dvd_of_le (subgroupOf_le_stabilizer hy)

/-- If `V ∩ U` has finite index in `U`, every element of `M^V` has a finite `U`-orbit, and so is
integral over `M^U`. -/
theorem finite_orbit_of_mem_fixedField {y : M} (hy : y ∈ fixedField V) (h : V.relIndex U ≠ 0) :
    (orbit U y).Finite := by
  refine Set.finite_of_ncard_ne_zero ?_
  rw [← index_stabilizer]
  exact ne_zero_of_dvd_ne_zero h (Subgroup.index_dvd_of_le (subgroupOf_le_stabilizer hy))

/-- **Fixed fields form separable extensions**: for `V ≤ U`, if `M^V` is integral over `M^U`, then
it is separable over `M^U`, whatever the characteristic. -/
theorem isSeparable_extendScalars_fixedField (hVU : V ≤ U)
    [Algebra.IsIntegral (fixedField U) (extendScalars (fixedField_le hVU))] :
    Algebra.IsSeparable (fixedField U) (extendScalars (fixedField_le hVU)) :=
  ⟨fun y ↦ by
    rw [IsSeparable, minpoly_eq]
    exact isSeparable_fixedField_of_isIntegral
      ((Algebra.IsIntegral.isIntegral y).map (val (extendScalars (fixedField_le hVU))))⟩

-- For `V ≤ U` of finite index, `M^V` is integral over `M^U`.
private theorem isIntegral_extendScalars_fixedField (hVU : V ≤ U) (h : V.relIndex U ≠ 0) :
    Algebra.IsIntegral (fixedField U) (extendScalars (fixedField_le hVU)) :=
  ⟨fun y ↦ by
    rw [← isIntegral_algHom_iff (val _) (val _).injective]
    exact isIntegral_fixedField_of_finite_orbit (finite_orbit_of_mem_fixedField y.2 h)⟩

/-- **A subgroup of finite index has a finite fixed field**: if `V ≤ U` has finite index, then
`M^V` is a finite extension of `M^U`. -/
theorem finiteDimensional_fixedField_of_relIndex_ne_zero (hVU : V ≤ U) (h : V.relIndex U ≠ 0) :
    FiniteDimensional (fixedField U) (extendScalars (fixedField_le hVU)) := by
  set E := extendScalars (fixedField_le hVU)
  have := isIntegral_extendScalars_fixedField hVU h
  have := isSeparable_extendScalars_fixedField hVU
  -- an infinite separable extension has finite subextensions of arbitrarily large degree, and a
  -- primitive element of one of them would have degree larger than `[U : V]`
  by_contra hfin
  obtain ⟨L, hL, hn⟩ := exists_lt_finrank_of_infinite_dimensional hfin (V.relIndex U)
  have := Algebra.isSeparable_tower_bot_of_isSeparable (fixedField U) L E
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (fixedField U) L
  rw [← (Field.primitive_element_iff_minpoly_natDegree_eq _ α).mp hα,
    minpoly_eq, minpoly_eq] at hn
  exact hn.not_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero h)
    (natDegree_minpoly_fixedField_dvd_relIndex (α : E).2))

/-- **A subgroup of finite index has a separable fixed field**: if `V ≤ U` has finite index, then
`M^V` is a separable extension of `M^U`. -/
theorem isSeparable_fixedField_of_relIndex_ne_zero (hVU : V ≤ U) (h : V.relIndex U ≠ 0) :
    Algebra.IsSeparable (fixedField U) (extendScalars (fixedField_le hVU)) :=
  have := finiteDimensional_fixedField_of_relIndex_ne_zero hVU h
  isSeparable_extendScalars_fixedField hVU

/-- **The degree of the fixed field of a subgroup of finite index divides the index**: for
`V ≤ U`, the degree `[M^V : M^U]` divides `[U : V]`. If `[U : V]` is infinite the statement says
nothing, since `relIndex` is then `0`. -/
theorem relfinrank_fixedField_dvd_relIndex (hVU : V ≤ U) :
    (fixedField U).relfinrank (fixedField V) ∣ V.relIndex U := by
  rcases eq_or_ne (V.relIndex U) 0 with h | h
  · rw [h]
    exact dvd_zero _
  set E := extendScalars (fixedField_le hVU)
  have := finiteDimensional_fixedField_of_relIndex_ne_zero hVU h
  have := isSeparable_extendScalars_fixedField hVU
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (fixedField U) E
  rw [relfinrank_eq_finrank_of_le (fixedField_le hVU),
    ← (Field.primitive_element_iff_minpoly_natDegree_eq _ α).mp hα, minpoly_eq]
  exact natDegree_minpoly_fixedField_dvd_relIndex α.2

/-- **The degree of the fixed field of a subgroup of finite index is at most the index**: for
`V ≤ U` with `[U : V]` finite, `[M^V : M^U] ≤ [U : V]`. -/
theorem relfinrank_fixedField_le_relIndex (hVU : V ≤ U) (h : V.relIndex U ≠ 0) :
    (fixedField U).relfinrank (fixedField V) ≤ V.relIndex U :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero h) (relfinrank_fixedField_dvd_relIndex hVU)

-- If `M^V` is finite over `M^U` and `V` is closed, a primitive element of `M^V` over `M^U` has
-- stabilizer `V ∩ U` in `U`, so its degree is `[U : V]`.
private theorem relIndex_eq_finrank_of_fixingSubgroup_eq (hVU : V ≤ U)
    (hV : (fixedField V).fixingSubgroup = V)
    [FiniteDimensional (fixedField U) (extendScalars (fixedField_le hVU))] :
    V.relIndex U = Module.finrank (fixedField U) (extendScalars (fixedField_le hVU)) := by
  set E := extendScalars (fixedField_le hVU)
  have := isSeparable_extendScalars_fixedField hVU
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (fixedField U) E
  have hE : (fixedField U)⟮(α : M)⟯ = E := by
    rw [← lift_adjoin_simple, hα, lift_top]
  -- an element of `U` fixing `α` fixes `(fixedField U)⟮α⟯ = M^V`, so lies in the closed `V`
  have hstab : stabilizer U (α : M) = V.subgroupOf U := by
    refine le_antisymm (fun u hu ↦ ?_) (subgroupOf_le_stabilizer α.2)
    set σ := fixingSubgroupEquiv (fixedField U) ⟨u, mem_fixingSubgroup_fixedField U u⟩
    have hσ : σ ∈ ((fixedField U)⟮(α : M)⟯).fixingSubgroup := by
      rw [fixingSubgroup_adjoin_simple, mem_stabilizer_iff, AlgEquiv.smul_def,
        coe_fixingSubgroupEquiv_apply]
      simpa [Subgroup.smul_def, AlgEquiv.smul_def] using hu
    rw [Subgroup.mem_subgroupOf, ← hV, mem_fixingSubgroup_iff]
    intro z hz
    have hzE : z ∈ (fixedField U)⟮(α : M)⟯ := by
      rw [hE, mem_extendScalars]
      exact hz
    simpa [σ] using (mem_fixingSubgroup_iff _ _).mp hσ z hzE
  rw [Subgroup.relIndex, ← hstab, ← natDegree_minpoly_fixedField_eq_index_stabilizer,
    ← minpoly_eq, (Field.primitive_element_iff_minpoly_natDegree_eq _ α).mp hα]

/-- **The degree of the fixed field of a closed subgroup is its index**: if `V ≤ U` and `V` is
the full group of automorphisms fixing `M^V`, then `[M^V : M^U] = [U : V]`. Here `V` may have
infinite index, and then `M^V / M^U` is an infinite extension, so that both sides are `0`. -/
theorem relfinrank_fixedField_eq_relIndex (hVU : V ≤ U) (hV : (fixedField V).fixingSubgroup = V) :
    (fixedField U).relfinrank (fixedField V) = V.relIndex U := by
  rw [relfinrank_eq_finrank_of_le (fixedField_le hVU)]
  by_cases hfin : FiniteDimensional (fixedField U) (extendScalars (fixedField_le hVU))
  · exact (relIndex_eq_finrank_of_fixingSubgroup_eq hVU hV).symm
  · rw [Module.finrank_of_infinite_dimensional hfin, eq_comm]
    by_contra h
    exact hfin (finiteDimensional_fixedField_of_relIndex_ne_zero hVU h)

end FiniteIndex

end IntermediateField
