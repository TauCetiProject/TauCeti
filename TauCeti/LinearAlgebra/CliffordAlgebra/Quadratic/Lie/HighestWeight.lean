/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.RootWeights
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Vector
import TauCeti.LinearAlgebra.CliffordAlgebra.Annihilation
import TauCeti.LinearAlgebra.CliffordAlgebra.PBW

/-!
# The highest weight vector of weight `ρ` in Kostant's module

Let `L` be a Killing-semisimple Lie algebra with Cartan subalgebra `H`, and fix a base of its root
system, with positive nilradical `n⁺`, which is totally isotropic for the Killing form. This file
proves that in Kostant's left-regular module, every nonzero element `c` annihilated by the
generators `ι y`, `y ∈ n⁺`, is a highest weight vector of weight the half-sum `ρ` of the positive
roots.

Such elements exist: choosing a root vector `e α` for each positive root `α`, the ordered product
`e⁺ = ∏_{α > 0} ι (e α)` is one. In particular `ρ` occurs as a highest weight of Kostant's module,
whereas Kostant's theorem says that it is the only one.

The computation runs through the root-space form of the quadratic lift. On an element annihilated
by `ι y`, a bivector involving `y` acts by a scalar read off from the Killing form. So the lift of a
positive root vector acts on `c` by a sum of Killing pairings of vectors whose weights do not add up
to zero, which vanish; and the lift of `h ∈ H` acts by `1 / 2 • ∑_{α > 0} α h • tr π_α`, where the
trace of the projection `π_α` onto the line `L_α` is one.

## Main results

* `CliffordAlgebra.isHighestWeightVector_weylVector_kostant_of_forall_ι_mul_eq_zero`: a nonzero
  element annihilated by the generators of `n⁺` is a highest weight vector of weight `ρ`.
* `CliffordAlgebra.ι_mul_prod_map_ι_rootVector_eq_zero`: the generators of `n⁺` annihilate the
  product of the generators of positive root vectors.
* `CliffordAlgebra.isHighestWeightVector_weylVector_prod_map_ι_rootVector`: that product is a
  highest weight vector of weight `ρ`.
* `CliffordAlgebra.exists_isHighestWeightVector_weylVector_kostant`: Kostant's module has a highest
  weight vector of weight `ρ`.

## References

* B. Kostant, *Clifford algebra analogue of the Hopf--Koszul--Samelson theorem*, Adv. Math. 125
  (1997), 275--350.
* E. Meinrenken, *Clifford Algebras and Lie Theory*, Springer Ergebnisse 58 (2013), Chapters
  5--10.
-/

public section

universe u v

open TauCeti LieAlgebra LieModule TauCeti.LieAlgebra

namespace CliffordAlgebra

open scoped CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} [Field K] {L : Type v} [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [Invertible (2 : K)] [LieAlgebra.IsKilling K L]

/-! ### Bivectors on elements annihilated by a generator -/

section Bivector

variable {x y : L} {c : CliffordAlgebra (killingQuadraticForm K L)}

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
private theorem bivector_mul_eq_killingForm_smul_left
    (hc : ι (killingQuadraticForm K L) x * c = 0) (y : L) :
    bivector (killingQuadraticForm K L) x y * c = killingForm K L x y • c := by
  rw [bivector_mul_eq_smul_of_ι_mul_eq_zero_left hc, polar_killingQuadraticForm, ← mul_assoc,
    invOf_mul_self, one_mul]

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
private theorem bivector_mul_eq_zero_right
    (hc : ι (killingQuadraticForm K L) y * c = 0) (h : killingForm K L x y = 0) :
    bivector (killingQuadraticForm K L) x y * c = 0 := by
  rw [bivector_mul_eq_smul_of_ι_mul_eq_zero_right x hc, polar_killingQuadraticForm, h]
  simp

end Bivector

variable [CharZero K] [IsAlgClosed K]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  {base : (IsKilling.rootSystem H).Base}
  {c : CliffordAlgebra (killingQuadraticForm K L)}

/-! ### The action of the quadratic lift -/

/-- The Cartan subalgebra acts through `ρ` on an element annihilated by the generators of `n⁺`. -/
private theorem adjointCliffordHom_cartan_mul_eq_smul
    (hc : ∀ y ∈ positiveNilradical H base, ι (killingQuadraticForm K L) y * c = 0) (h : H) :
    adjointCliffordHom K L (h : L) * c = weylVector (IsKilling.rootSystem H) base h • c := by
  classical
  let bs := Module.finBasis K L
  have hroot (a : H.root) (ha : a ∈ posRootsFinset (IsKilling.rootSystem H) base) :
      (∑ i, bivector (killingQuadraticForm K L)
        (genWeightSpaceProjection K H L (a : H.root) (bs i))
        (genWeightSpaceProjection K H L (-(a : H.root)) (killingDualBasis bs i))) * c = c := by
    rw [Finset.sum_mul, Finset.sum_congr rfl fun i _ ↦ bivector_mul_eq_killingForm_smul_left
      (hc _ (mem_positiveNilradical_of_mem_rootSpace H base
        ((mem_posRootsFinset _ base a).mp ha) (genWeightSpaceProjection_apply_mem _ _))) _,
      ← Finset.sum_smul, sum_killingForm_genWeightSpaceProjection_eq_one H bs
        (H.isNonZero_coe_root a), one_smul]
  have hsum : adjointCliffordHom K L (h : L) * c =
      (2 : K)⁻¹ • ∑ a ∈ posRootsFinset (IsKilling.rootSystem H) base,
        ((a : H.root) : Weight K H L) h • c := by
    rw [adjointCliffordHom_cartan_eq_sum_posRoots H bs base h, smul_mul_assoc, Finset.sum_mul]
    exact congrArg _ (Finset.sum_congr rfl fun a ha ↦ by rw [smul_mul_assoc, hroot a ha])
  have hscalar : weylVector (IsKilling.rootSystem H) base h =
      (2 : K)⁻¹ * ∑ a ∈ posRootsFinset (IsKilling.rootSystem H) base,
        ((a : H.root) : Weight K H L) h := by
    simp [weylVector_def, twoWeylVector_def, LinearMap.sum_apply]
  rw [hsum, hscalar, mul_smul, Finset.sum_smul]

omit [IsAlgClosed K] in
/-- A bivector in the root-space form of the lift of a positive root vector kills an element
annihilated by the generators of `n⁺`: its two vectors are Killing-orthogonal, and one of them lies
in `n⁺`. -/
private theorem bivector_lie_mul_eq_zero
    (hc : ∀ y ∈ positiveNilradical H base, ι (killingQuadraticForm K L) y * c = 0)
    {α : H.root} (hα : α ∈ posRoots (IsKilling.rootSystem H) base) {x : L}
    (hx : x ∈ rootSpace H (α : H → K)) (χ : Weight K H L) {u v : L}
    (hu : u ∈ rootSpace H (χ : H → K)) (hv : v ∈ rootSpace H ((-χ : Weight K H L) : H → K)) :
    bivector (killingQuadraticForm K L) ⁅x, u⁆ v * c = 0 := by
  have hbracket : ⁅x, u⁆ ∈ rootSpace H ((α : H → K) + (χ : H → K)) :=
    lie_mem_genWeightSpace_of_mem_genWeightSpace hx hu
  have hkilling : killingForm K L ⁅x, u⁆ v = 0 := by
    refine killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero K L H hbracket hv fun h ↦ ?_
    refine H.isNonZero_coe_root α (funext fun z ↦ ?_)
    simpa using congrFun h z
  have hxn := mem_positiveNilradical_of_mem_rootSpace H base hα hx
  -- Either `v` lies in `n⁺`, or `u` lies in the Borel subalgebra and hence `⁅x, u⁆` lies in `n⁺`.
  by_cases hv' : v ∈ positiveNilradical H base
  · exact bivector_mul_eq_zero_right (hc v hv') hkilling
  have hub : u ∈ borelSubalgebra H base := by
    by_cases hχ : χ.IsZero
    · refine le_borelSubalgebra H base ?_
      rw [hχ.eq, rootSpace_zero_eq K L H] at hu
      simpa using hu
    · let a : H.root := ⟨χ, by simpa [LieSubalgebra.root] using hχ⟩
      refine positiveNilradical_le_borelSubalgebra H base
        (mem_positiveNilradical_of_mem_rootSpace H base (α := a) ?_ hu)
      by_contra ha
      have hneg := neg_mem_posRoots_of_mem_negRoots base
        ((not_mem_posRoots_iff_mem_negRoots _ base a).mp ha)
      refine hv' (mem_positiveNilradical_of_mem_rootSpace H base hneg ?_)
      rwa [IsKilling.val_neg_root]
  have hmem : ⁅x, u⁆ ∈ positiveNilradical H base := by
    rw [← lie_skew]
    exact neg_mem (lie_mem_positiveNilradical_of_mem_borelSubalgebra H base hub hxn)
  rw [bivector_mul_eq_killingForm_smul_left (hc _ hmem), hkilling, zero_smul]

omit [IsAlgClosed K] in
/-- The positive root spaces act by zero on an element annihilated by the generators of `n⁺`. -/
private theorem adjointCliffordHom_mul_eq_zero_of_mem_rootSpace
    (hc : ∀ y ∈ positiveNilradical H base, ι (killingQuadraticForm K L) y * c = 0)
    {α : H.root} (hα : α ∈ posRoots (IsKilling.rootSystem H) base) {x : L}
    (hx : x ∈ rootSpace H (α : H → K)) :
    adjointCliffordHom K L x * c = 0 := by
  classical
  rw [adjointCliffordHom_eq_sum_weight H (Module.finBasis K L) x, smul_mul_assoc, Finset.sum_mul,
    Finset.sum_eq_zero, smul_zero]
  intro χ _
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [adjointBivector_apply]
  exact bivector_lie_mul_eq_zero hc hα hx χ (genWeightSpaceProjection_apply_mem _ _)
    (genWeightSpaceProjection_apply_mem _ _)

/-- **An element annihilated by the generators of `n⁺` is a highest weight vector of weight `ρ`** in
Kostant's left-regular module, if it is nonzero. -/
theorem isHighestWeightVector_weylVector_kostant_of_forall_ι_mul_eq_zero (hc0 : c ≠ 0)
    (hc : ∀ y ∈ positiveNilradical H base, ι (killingQuadraticForm K L) y * c = 0) :
    IsHighestWeightVector base (weylVector (IsKilling.rootSystem H) base) c :=
  isHighestWeightVector_of_forall_rootSpace hc0
    (fun h ↦ by rw [kostant_lie_def, adjointCliffordHom_cartan_mul_eq_smul hc])
    fun _ hα _ hx ↦ by
      rw [kostant_lie_def, adjointCliffordHom_mul_eq_zero_of_mem_rootSpace hc hα hx]

/-! ### The product of the generators of positive root vectors -/

section RootVectors

variable (e : H.root → L) (he : ∀ α ∈ posRoots (IsKilling.rootSystem H) base,
    e α ∈ rootSpace H (α : H → K))
  (he0 : ∀ α ∈ posRoots (IsKilling.rootSystem H) base, e α ≠ 0)
  {l : List H.root} (hmem : ∀ α, α ∈ l ↔ α ∈ posRoots (IsKilling.rootSystem H) base)

include he he0 hmem in
omit [Invertible (2 : K)] [IsAlgClosed K] in
/-- **The generators of `n⁺` annihilate the product of the generators of positive root vectors**:
each root space is the line through its root vector, and each root vector is an isotropic factor
orthogonal to the others. -/
theorem ι_mul_prod_map_ι_rootVector_eq_zero {y : L} (hy : y ∈ positiveNilradical H base) :
    ι (killingQuadraticForm K L) y * ((l.map e).map (ι (killingQuadraticForm K L))).prod = 0 := by
  rw [mem_positiveNilradical, rootSpaceSpan_eq_iSup] at hy
  refine LieSubmodule.iSup_induction _ hy (motive := fun y ↦ ι (killingQuadraticForm K L) y *
    ((l.map e).map (ι (killingQuadraticForm K L))).prod = 0) (fun ⟨α, hα⟩ y hy ↦ ?_) (by simp)
    fun _ _ h₁ h₂ ↦ by rw [map_add, add_mul, h₁, h₂, add_zero]
  have hspan := IsKilling.toSubmodule_rootSpace_eq_span (α : Weight K H L)
    (H.isNonZero_coe_root α) (e α) (he0 α hα) (he α hα)
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp (hspan.le hy)
  have hortho : ∀ x ∈ l.map e, (killingQuadraticForm K L).IsOrtho (e α) x := by
    intro x hx
    obtain ⟨β, hβ, rfl⟩ := List.mem_map.mp hx
    have hβ' := (hmem β).mp hβ
    rw [← QuadraticMap.isOrtho_polarBilin, QuadraticMap.polarBilin_apply_apply,
      polar_killingQuadraticForm, killingForm_eq_zero_of_mem_posRoots hα hβ' (he α hα) (he β hβ'),
      mul_zero]
  have hself : killingQuadraticForm K L (e α) = 0 := by
    rw [killingQuadraticForm_apply]
    exact killingForm_eq_zero_of_mem_posRoots hα hα (he α hα) (he α hα)
  rw [map_smul, smul_mul_assoc, ι_mul_prod_map_ι_eq_zero
    (List.mem_map_of_mem ((hmem α).mpr hα)) hself hortho, smul_zero]

include he he0 hmem in
/-- **The ordered product `e⁺ = ∏_{α > 0} ι (e α)` is a highest weight vector of weight `ρ`** in
Kostant's left-regular module, for any choice of root vectors and any order of the positive roots.
-/
theorem isHighestWeightVector_weylVector_prod_map_ι_rootVector (hl : l.Nodup) :
    IsHighestWeightVector base (weylVector (IsKilling.rootSystem H) base)
      ((l.map e).map (ι (killingQuadraticForm K L))).prod := by
  refine isHighestWeightVector_weylVector_kostant_of_forall_ι_mul_eq_zero ?_
    fun y hy ↦ ι_mul_prod_map_ι_rootVector_eq_zero e he he0 hmem hy
  -- Root vectors are nonzero vectors of independent root spaces, hence linearly independent.
  have hind : iSupIndep fun i : Fin l.length ↦
      (rootSpace H ((l.get i : H.root) : H → K) : Submodule K L) :=
    (LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace K H L)).comp
      (f := fun i : Fin l.length ↦ ((l.get i : H.root) : H → K)) fun i j hij ↦
        hl.injective_get (Subtype.ext (DFunLike.coe_injective hij))
  have hv : LinearIndependent K fun i : Fin l.length ↦ e (l.get i) :=
    hind.linearIndependent _ (fun i ↦ he _ ((hmem _).mp (l.get_mem i)))
      fun i ↦ he0 _ ((hmem _).mp (l.get_mem i))
  have hne := prod_map_ι_ofFn_ne_zero (killingQuadraticForm K L) _ hv
  have hlist : (List.ofFn fun i : Fin l.length ↦ e (l.get i)) = l.map e :=
    List.ofFn_getElem_eq_map l e
  rwa [← List.map_ofFn, hlist] at hne

end RootVectors

variable (base) in
/-- **Kostant's module has a highest weight vector of weight `ρ`.** -/
theorem exists_isHighestWeightVector_weylVector_kostant :
    ∃ c : CliffordAlgebra (killingQuadraticForm K L),
      IsHighestWeightVector base (weylVector (IsKilling.rootSystem H) base) c := by
  classical
  choose e he he0 using fun α : H.root ↦ Weight.exists_ne_zero (R := K) (L := H) (M := L) α.1
  exact ⟨_, isHighestWeightVector_weylVector_prod_map_ι_rootVector (l :=
    (posRootsFinset (IsKilling.rootSystem H) base).toList) e (fun α _ ↦ he α) (fun α _ ↦ he0 α)
    (fun α ↦ by rw [Finset.mem_toList, mem_posRootsFinset])
    (Finset.nodup_toList _)⟩

end CliffordAlgebra
