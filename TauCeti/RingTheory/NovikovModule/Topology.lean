/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Bilinear
public import TauCeti.RingTheory.NovikovSeries.TopologicalRing
public import Mathlib.Topology.Algebra.Module.TransferInstance

/-!
# The potential-cutoff topology on completed combinations

For a potential `F : S → ℝ`, a completed combination `a ∈ NovikovModule R F` is small when its
coefficients vanish at every generator of potential above a low cutoff. For a real cutoff `C`, the
combinations vanishing above `C` form an additive subgroup `U_C`
(`TauCeti.NovikovModule.potentialFiltration`). These subgroups increase with `C` and meet only in
`0`; as `C → -∞` they form a basis of neighbourhoods of `0` for a separated group topology, the
*potential-cutoff topology*. A family converges in it when, above every potential cutoff, all of
its coefficients eventually agree with those of the limit.

The completed combinations are complete for this topology, and the finite combinations are dense:
a completed combination differs from its truncation above `C` by an element of `U_C`. The topology
is defined without choosing orbit lifts. When `S` is a finite disjoint union of torsors with
equivariant potential, coordinates in any chosen lifts identify it with the product of the period
topologies on Novikov series, so the lift-independent Novikov scalar action is continuous.

The maps and products of completed combinations given by supported kernels
(`TauCeti.NovikovModule.kernelMap`, `TauCeti.NovikovModule.kernelProduct`) shift potential
cutoffs by the constant of their potential bound. Hence a kernel map is continuous, and a kernel
product is jointly continuous in both inputs. Floer and Novikov differentials, continuation maps,
chain homotopies and the pair-of-pants product are of this form, so they are continuous for the
potential-cutoff topologies of their complexes.

The filter-basis construction and the completeness argument parallel
`TauCeti.RingTheory.NovikovSeries.Topology`, with cutoffs directed towards `-∞` instead of `+∞`.
The truncation, topology and coordinate parts, including `NovikovModule.ofFinsupp` and
`NovikovModule.trunc` in `TauCeti.RingTheory.NovikovModule.Basic`, adapt the approach of the
unmerged TauCeti PR https://github.com/TauCetiProject/TauCeti/pull/20410; the kernel-map and
kernel-product continuity results are new.

## Main definitions

* `TauCeti.NovikovModule.potentialFiltration R F C`: the subgroup `U_C` of completed combinations
  vanishing at every generator of potential `> C`.
* The instances `TopologicalSpace`, `IsTopologicalAddGroup`, `UniformSpace` and
  `IsUniformAddGroup` on `TauCeti.NovikovModule R F`: the potential-cutoff topology.
* `TauCeti.NovikovModule.coordinatesContinuousLinearEquiv`: coordinates in chosen orbit lifts, as
  a continuous Novikov-linear equivalence.

## Main results

* `TauCeti.NovikovModule.tendsto_nhds_iff`: convergence means eventual agreement of the
  coefficients above every potential cutoff.
* The instances `T2Space`, `CompleteSpace`, `NonarchimedeanAddGroup` and `ContinuousConstSMul`.
* `TauCeti.NovikovModule.continuous_of_forall_mem_potentialFiltration`: an additive map sending
  some `U_D` into each `U_E` is continuous.
* `TauCeti.NovikovModule.denseRange_ofFinsupp`: finite combinations are dense.
* `TauCeti.NovikovModule.continuousSMul_module`: the Novikov scalar action is continuous.
* `TauCeti.NovikovModule.continuous_kernelMap`: kernel maps are continuous.
* `TauCeti.NovikovModule.continuous_kernelProduct`: kernel products are jointly continuous.
* `TauCeti.NovikovModule.continuous_kernelProduct_left`,
  `TauCeti.NovikovModule.continuous_kernelProduct_right`: continuity in each input separately.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2.
* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 3.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the pair-of-pants product.
-/

public section

noncomputable section

open Filter Function Set Topology Uniformity

namespace TauCeti

namespace NovikovModule

variable {R S : Type*} [Ring R] {F : S → ℝ}

section Filtration

variable {C : ℝ} {a : NovikovModule R F}

variable (R F) in
/-- The additive subgroup `U_C` of completed combinations whose coefficients vanish at every
generator of potential `> C`. These subgroups form a basis of neighbourhoods of `0` in the
potential-cutoff topology as `C → -∞`. -/
def potentialFiltration (C : ℝ) : AddSubgroup (NovikovModule R F) where
  carrier := {a | ∀ s, C < F s → a.val s = 0}
  add_mem' ha hb s hs := by simp [ha s hs, hb s hs]
  zero_mem' _ _ := rfl
  neg_mem' ha s hs := by simp [ha s hs]

@[simp]
theorem mem_potentialFiltration : a ∈ potentialFiltration R F C ↔ ∀ s, C < F s → a.val s = 0 :=
  Iff.rfl

theorem monotone_potentialFiltration : Monotone (potentialFiltration R F) :=
  fun _ _ hCD _ ha s hs => ha s (hCD.trans_lt hs)

/-- Every completed combination lies in some `U_C`, since the potential is bounded above on its
support. -/
theorem exists_mem_potentialFiltration (a : NovikovModule R F) :
    ∃ C, a ∈ potentialFiltration R F C := by
  obtain ⟨C, hC⟩ := bddAbove_image_support a
  exact ⟨C, fun s hs => by_contra fun ha => (hC ⟨s, ha, rfl⟩).not_gt hs⟩

/-- An element of every `U_C` is zero. -/
theorem eq_zero_of_forall_mem_potentialFiltration (ha : ∀ C, a ∈ potentialFiltration R F C) :
    a = 0 :=
  Subtype.ext <| funext fun s => ha (F s - 1) s (sub_one_lt _)

/-- Each `U_C` is closed under multiplication by a ground-ring scalar. -/
theorem smul_mem_potentialFiltration (c : R) (ha : a ∈ potentialFiltration R F C) :
    c • a ∈ potentialFiltration R F C := fun s hs => by
  simp [ha s hs]

/-- A completed combination differs from its truncation above `C` by an element of `U_C`. -/
theorem sub_ofFinsupp_trunc_mem_potentialFiltration (C : ℝ) (a : NovikovModule R F) :
    a - ofFinsupp F (trunc C a) ∈ potentialFiltration R F C := fun s hs => by
  simp [trunc_apply_of_lt hs]

end Filtration

section Topology

variable (R F) in
/-- The additive group filter basis made of the subgroups `U_C`, which defines the
potential-cutoff topology. -/
@[instance_reducible]
def potentialFilterBasis : AddGroupFilterBasis (NovikovModule R F) :=
  addGroupFilterBasisOfComm (range fun C => (potentialFiltration R F C : Set _))
    (range_nonempty _)
    (by
      rintro _ _ ⟨C, rfl⟩ ⟨D, rfl⟩
      exact ⟨_, mem_range_self (min C D),
        subset_inter (monotone_potentialFiltration (min_le_left C D))
          (monotone_potentialFiltration (min_le_right C D))⟩)
    (by
      rintro _ ⟨C, rfl⟩
      exact zero_mem (potentialFiltration R F C))
    (by
      rintro _ ⟨C, rfl⟩
      exact ⟨_, mem_range_self C, by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        exact add_mem ha hb⟩)
    (by
      rintro _ ⟨C, rfl⟩
      exact ⟨_, mem_range_self C, fun a ha => neg_mem ha⟩)

/-- The potential-cutoff topology on completed combinations: the subgroups `U_C` form a basis of
neighbourhoods of `0`. -/
instance : TopologicalSpace (NovikovModule R F) :=
  (potentialFilterBasis R F).topology

instance : IsTopologicalAddGroup (NovikovModule R F) :=
  (potentialFilterBasis R F).isTopologicalAddGroup

/-- The uniform structure of the potential-cutoff topology. Its entourages are generated by the
sets `{(a, b) | b - a ∈ U_C}` for real cutoffs `C`: `a` and `b` are `C`-close when their
coefficients agree at every generator of potential `> C`. -/
instance : UniformSpace (NovikovModule R F) :=
  IsTopologicalAddGroup.rightUniformSpace _

instance : IsUniformAddGroup (NovikovModule R F) :=
  isUniformAddGroup_of_addCommGroup

/- When the coefficient ring has its own topology, as `ℤ` does, the carrier is also a subtype of
the product space `S → R`, whose coefficientwise topology is a different instance. These checks
pin down that instance resolution selects the potential-cutoff structures. -/
example {S : Type*} (F : S → ℝ) :
    (inferInstance : TopologicalSpace (NovikovModule ℤ F)) = (potentialFilterBasis ℤ F).topology :=
  rfl

example {S : Type*} (F : S → ℝ) :
    (inferInstance : UniformSpace (NovikovModule ℤ F)) =
      IsTopologicalAddGroup.rightUniformSpace (NovikovModule ℤ F) :=
  rfl

/-- The subgroups `U_C` form a basis of neighbourhoods of `0` in the potential-cutoff
topology. -/
theorem hasBasis_nhds_zero :
    (𝓝 (0 : NovikovModule R F)).HasBasis (fun _ : ℝ => True)
      fun C => (potentialFiltration R F C : Set (NovikovModule R F)) := by
  refine ((potentialFilterBasis R F).nhds_zero_hasBasis).to_hasBasis ?_ ?_
  · rintro _ ⟨C, rfl⟩
    exact ⟨C, trivial, subset_rfl⟩
  · exact fun C _ => ⟨_, mem_range_self C, subset_rfl⟩

theorem potentialFiltration_mem_nhds_zero (C : ℝ) :
    (potentialFiltration R F C : Set (NovikovModule R F)) ∈ 𝓝 0 :=
  hasBasis_nhds_zero.mem_of_mem trivial

theorem isOpen_potentialFiltration (C : ℝ) :
    IsOpen (potentialFiltration R F C : Set (NovikovModule R F)) :=
  AddSubgroup.isOpen_of_mem_nhds _ (potentialFiltration_mem_nhds_zero C)

theorem isClosed_potentialFiltration (C : ℝ) :
    IsClosed (potentialFiltration R F C : Set (NovikovModule R F)) :=
  AddSubgroup.isClosed_of_isOpen _ (isOpen_potentialFiltration C)

/-- The sets `{b | b - a ∈ U_C}` form a basis of neighbourhoods of `a` in the potential-cutoff
topology. -/
theorem hasBasis_nhds (a : NovikovModule R F) :
    (𝓝 a).HasBasis (fun _ : ℝ => True) fun C => {b | b - a ∈ potentialFiltration R F C} := by
  rw [← nhds_translation_sub a]
  exact hasBasis_nhds_zero.comap _

/-- The entourages `{(a, b) | b - a ∈ U_C}` form a basis of the potential-cutoff uniformity. -/
theorem hasBasis_uniformity :
    (𝓤 (NovikovModule R F)).HasBasis (fun _ : ℝ => True)
      fun C => {p | p.2 - p.1 ∈ potentialFiltration R F C} := by
  rw [uniformity_eq_comap_nhds_zero]
  exact hasBasis_nhds_zero.comap _

/-- A family of completed combinations converges to `a` in the potential-cutoff topology if and
only if, above every potential cutoff, its coefficients eventually agree with those of `a`. -/
theorem tendsto_nhds_iff {ι : Type*} {l : Filter ι} {f : ι → NovikovModule R F}
    {a : NovikovModule R F} :
    Tendsto f l (𝓝 a) ↔ ∀ C : ℝ, ∀ᶠ i in l, ∀ s, C < F s → (f i).val s = a.val s := by
  simp [(hasBasis_nhds a).tendsto_right_iff, mem_potentialFiltration, sub_eq_zero]

instance : T2Space (NovikovModule R F) :=
  IsTopologicalAddGroup.t2Space_of_zero_sep fun a ha => by
    obtain ⟨s, hs⟩ : ∃ s, a.val s ≠ 0 := by
      by_contra! h
      exact ha (Subtype.ext (funext h))
    exact ⟨_, potentialFiltration_mem_nhds_zero (F s - 1), fun ha' =>
      hs (ha' s (sub_one_lt _))⟩

/-- An additive map between completed combinations is continuous for the potential-cutoff
topologies when, for every cutoff `E`, it sends some `U_D` into `U_E`. -/
theorem continuous_of_forall_mem_potentialFiltration {S' 𝓕 : Type*} {F' : S' → ℝ}
    [FunLike 𝓕 (NovikovModule R F) (NovikovModule R F')]
    [AddMonoidHomClass 𝓕 (NovikovModule R F) (NovikovModule R F')] (f : 𝓕)
    (hf : ∀ E, ∃ D, ∀ a ∈ potentialFiltration R F D, f a ∈ potentialFiltration R F' E) :
    Continuous f :=
  continuous_of_continuousAt_zero f <| by
    rw [ContinuousAt, map_zero]
    exact (hasBasis_nhds_zero.tendsto_iff hasBasis_nhds_zero).2 fun E _ =>
      (hf E).imp fun _ hD => ⟨trivial, hD⟩

/-- The potential-cutoff topology is nonarchimedean: the open subgroups `U_C` form a basis of
neighbourhoods of `0`. -/
instance : NonarchimedeanAddGroup (NovikovModule R F) where
  is_nonarchimedean U hU := by
    obtain ⟨C, -, hC⟩ := hasBasis_nhds_zero.mem_iff.1 hU
    exact ⟨⟨potentialFiltration R F C, isOpen_potentialFiltration C⟩, hC⟩

/-- Multiplication by a fixed ground-ring scalar is continuous in the potential-cutoff
topology. -/
instance : ContinuousConstSMul R (NovikovModule R F) where
  continuous_const_smul c :=
    (continuous_of_forall_mem_potentialFiltration
      (DistribSMul.toAddMonoidHom (NovikovModule R F) c) fun C =>
        ⟨C, fun _ ha => smul_mem_potentialFiltration c ha⟩).congr
      (DistribSMul.toAddMonoidHom_apply _ c)

/-- The coefficient of a completed combination at a generator is locally constant in the
potential-cutoff topology. -/
theorem isLocallyConstant_apply_val (s : S) :
    IsLocallyConstant fun a : NovikovModule R F => a.val s :=
  (IsLocallyConstant.iff_eventually_eq _).2 fun a => by
    filter_upwards [tendsto_nhds_iff.1 (tendsto_id (x := 𝓝 a)) (F s - 1)] with b hb
    exact hb s (sub_one_lt _)

/-- The completed combinations are complete for the potential-cutoff topology: the limit of a
Cauchy filter has, at each generator, the coefficient on which the filter eventually agrees. -/
instance : CompleteSpace (NovikovModule R F) := by
  refine ⟨fun {l} hl => ?_⟩
  obtain ⟨hne, hl⟩ := hasBasis_uniformity.cauchy_iff.1 hl
  choose U hUl hU using fun C => hl C trivial
  have hU' : ∀ C, ∀ a ∈ U C, ∀ b ∈ U C, ∀ s, C < F s → a.val s = b.val s :=
    fun C a ha b hb s hs => (sub_eq_zero.1 (hU C a ha b hb s hs)).symm
  choose x hx using fun C => hne.nonempty_of_mem (hUl C)
  -- The coefficient of the limit at `s` is read off from the set `U (F s - 1)`.
  have hcoeff : ∀ C, ∀ a ∈ U C, ∀ s, C < F s → a.val s = (x (F s - 1)).val s := by
    intro C a ha s hs
    obtain ⟨b, hbC, hbs⟩ := hne.nonempty_of_mem (inter_mem (hUl C) (hUl (F s - 1)))
    exact (hU' C a ha b hbC s hs).trans (hU' _ b hbs _ (hx _) s (sub_one_lt _))
  let lim : NovikovModule R F :=
    ⟨fun s => (x (F s - 1)).val s, mem_iff.2 fun C =>
      (finite_gt (x C) C).subset fun s hs => by
        refine ⟨?_, hs.2⟩
        rw [hcoeff C (x C) (hx C) s hs.2]
        exact hs.1⟩
  refine ⟨lim, (hasBasis_nhds lim).ge_iff.2 fun C _ =>
    mem_of_superset (hUl C) fun a ha s hs => ?_⟩
  simp [lim, hcoeff C a ha s hs]

/-- The truncations of a completed combination converge to it as the cutoff tends to `-∞`. -/
theorem tendsto_ofFinsupp_trunc (a : NovikovModule R F) :
    Tendsto (fun C => ofFinsupp F (trunc C a)) atBot (𝓝 a) :=
  (hasBasis_nhds a).tendsto_right_iff.2 fun C _ => by
    filter_upwards [eventually_le_atBot C] with D hD
    rw [← neg_mem_iff, neg_sub]
    exact monotone_potentialFiltration hD (sub_ofFinsupp_trunc_mem_potentialFiltration D a)

/-- The finite combinations are dense in the potential-cutoff topology. -/
theorem denseRange_ofFinsupp : DenseRange (ofFinsupp (R := R) F) :=
  fun a => mem_closure_of_tendsto (tendsto_ofFinsupp_trunc a)
    (Eventually.of_forall fun _ => mem_range_self _)

end Topology

section Coordinates

variable {H ι : Type*} [AddGroup H] [Finite ι] {P : ι → Type*}
    [∀ i, AddTorsor H (P i)] {N : H →+ ℝ} {F : (Σ i, P i) → ℝ}
    (hF : ∀ i h (p : P i), F ⟨i, h +ᵥ p⟩ = F ⟨i, p⟩ - N h) (r : ∀ i, P i)

/-- In lift coordinates, the subgroup `U_C` is the product of the period neighbourhoods
`U_(F(r i) - C)` of Novikov series, measured from the potential of each chosen lift. -/
theorem mem_potentialFiltration_iff_coordinates {C : ℝ} {a : NovikovModule R F} :
    a ∈ potentialFiltration R F C ↔
      ∀ i, coordinates hF r a i ∈ NovikovSeries.periodFiltration R N (F ⟨i, r i⟩ - C) := by
  simp only [mem_potentialFiltration, NovikovSeries.mem_periodFiltration]
  exact (coordinates_coeff_eq_zero_iff hF r a C).symm

/-- Coordinates in any chosen lifts are continuous for the potential-cutoff topology. -/
@[fun_prop]
theorem continuous_coordinates : Continuous (coordinates (R := R) hF r) := by
  refine continuous_pi fun i => continuous_iff_continuousAt.2 fun a =>
    NovikovSeries.tendsto_nhds_iff.2 fun C => ?_
  filter_upwards [tendsto_nhds_iff.1 (tendsto_id (x := 𝓝 a)) (F ⟨i, r i⟩ - C)] with b hb h hh
  simpa only [coordinates_coeff, id_eq] using hb ⟨i, h +ᵥ r i⟩ (by rw [hF]; linarith)

/-- Reconstructing a completed combination from its coordinates in chosen lifts is continuous. -/
@[fun_prop]
theorem continuous_coordinates_symm : Continuous (coordinates (R := R) hF r).symm := by
  refine continuous_iff_continuousAt.2 fun b => tendsto_nhds_iff.2 fun C => ?_
  have hi : ∀ i, ∀ᶠ b' in 𝓝 b, ∀ h, N h < F ⟨i, r i⟩ - C →
      (b' i).coeff h = (b i).coeff h := fun i =>
    NovikovSeries.tendsto_nhds_iff.1 ((continuous_apply i).tendsto b) _
  filter_upwards [eventually_all.2 hi] with b' hb ⟨i, p⟩ hp
  simp only [coordinates_symm_apply]
  exact hb i (p -ᵥ r i) (by linarith [potential_eq_sub_vsub hF r i p])

/-- Coordinates in chosen orbit lifts, as a continuous Novikov-linear equivalence between the
completed combinations with the potential-cutoff topology and the finite product of Novikov
series with the period topology. -/
def coordinatesContinuousLinearEquiv :
    letI := module (R := R) hF
    NovikovModule R F ≃L[NovikovSeries R H N] (ι → NovikovSeries R H N) :=
  letI := module (R := R) hF
  { coordinatesLinearEquiv hF r with
    continuous_toFun := by
      rw [LinearEquiv.toFun_eq_coe]
      exact (continuous_coordinates hF r).congr fun a =>
        (coordinatesLinearEquiv_apply hF r a).symm
    continuous_invFun := by
      rw [LinearEquiv.invFun_eq_symm]
      exact (continuous_coordinates_symm hF r).congr fun b =>
        (coordinatesLinearEquiv_symm_apply hF r b).symm }

@[simp]
theorem coordinatesContinuousLinearEquiv_apply (a : NovikovModule R F) :
    coordinatesContinuousLinearEquiv hF r a = coordinates hF r a := by
  simp [coordinatesContinuousLinearEquiv]

@[simp]
theorem coordinatesContinuousLinearEquiv_symm_apply (b : ι → NovikovSeries R H N) :
    letI := module (R := R) hF
    (coordinatesContinuousLinearEquiv hF r).symm b = (coordinates hF r).symm b := by
  let := module (R := R) hF
  rw [← ContinuousLinearEquiv.coe_symm_toLinearEquiv]
  exact coordinatesLinearEquiv_symm_apply hF r b

omit r in
/-- The Novikov scalar action on completed combinations is continuous for the potential-cutoff
topology. -/
theorem continuousSMul_module :
    letI := module (R := R) hF
    ContinuousSMul (NovikovSeries R H N) (NovikovModule R F) :=
  letI := module (R := R) hF
  (coordinatesContinuousLinearEquiv hF fun i => Classical.arbitrary (P i)).continuousSMul

end Coordinates

section KernelMap

variable {S₁ S₀ : Type*} {F₁ : S₁ → ℝ} {F₀ : S₀ → ℝ} {C : ℝ} {m : S₁ → S₀ → R}
  (hm : ∀ p₁ p₀, m p₁ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + C)
  (hmfin : ∀ p₁, m p₁ ∈ NovikovModule R F₀)

/-- A kernel map with potential bound `C` sends `U_D` into `U_(D + C)`. -/
theorem kernelMap_mem_potentialFiltration {D : ℝ} {a : NovikovModule R F₁}
    (ha : a ∈ potentialFiltration R F₁ D) :
    kernelMap hm hmfin a ∈ potentialFiltration R F₀ (D + C) :=
  fun _ hp => kernelMap_apply_val_eq_zero hm hmfin ha hp

/-- A kernel map is continuous for the potential-cutoff topologies. -/
@[fun_prop]
theorem continuous_kernelMap : Continuous (kernelMap hm hmfin) :=
  continuous_of_forall_mem_potentialFiltration _ fun D =>
    ⟨D - C, fun a ha => by simpa using kernelMap_mem_potentialFiltration hm hmfin ha⟩

end KernelMap

section KernelProduct

variable {R S₁ S₂ S₀ : Type*} [CommRing R] {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₀ : S₀ → ℝ}
  {C : ℝ} {n : S₁ → S₂ → S₀ → R}
  (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
  (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)

/-- A kernel product with potential bound `C` sends `U_(D₁) × U_(D₂)` into `U_(D₁ + D₂ + C)`. -/
theorem kernelProduct_mem_potentialFiltration {D₁ D₂ : ℝ} {a : NovikovModule R F₁}
    {b : NovikovModule R F₂} (ha : a ∈ potentialFiltration R F₁ D₁)
    (hb : b ∈ potentialFiltration R F₂ D₂) :
    kernelProduct hn hfin a b ∈ potentialFiltration R F₀ (D₁ + D₂ + C) :=
  fun _ hp => kernelProduct_apply_val_eq_zero hn hfin ha hb hp

/-- A kernel product is continuous in its second input for the potential-cutoff topologies. -/
@[fun_prop]
theorem continuous_kernelProduct_right (a : NovikovModule R F₁) :
    Continuous (kernelProduct hn hfin a) := by
  obtain ⟨A, hA⟩ := exists_mem_potentialFiltration a
  exact continuous_of_forall_mem_potentialFiltration _ fun D =>
    ⟨D - A - C, fun b hb => monotone_potentialFiltration (le_of_eq (by ring))
      (kernelProduct_mem_potentialFiltration hn hfin hA hb)⟩

/-- A kernel product is continuous in its first input for the potential-cutoff topologies. -/
@[fun_prop]
theorem continuous_kernelProduct_left (b : NovikovModule R F₂) :
    Continuous fun a => kernelProduct hn hfin a b := by
  obtain ⟨B, hB⟩ := exists_mem_potentialFiltration b
  refine (continuous_of_forall_mem_potentialFiltration ((kernelProduct hn hfin).flip b)
    fun D => ⟨D - B - C, fun a ha => ?_⟩).congr fun a => LinearMap.flip_apply _ _ _
  rw [LinearMap.flip_apply]
  exact monotone_potentialFiltration (le_of_eq (by ring))
    (kernelProduct_mem_potentialFiltration hn hfin ha hB)

/-- A kernel product is jointly continuous in its two inputs for the potential-cutoff
topologies. -/
@[fun_prop]
theorem continuous_kernelProduct :
    Continuous fun p : NovikovModule R F₁ × NovikovModule R F₂ =>
      kernelProduct hn hfin p.1 p.2 := by
  -- `continuous_of_continuousAt_zero₂` needs the product as a bundled `→+` of `→+`.
  let B := LinearMap.toAddMonoidHom'.comp (kernelProduct hn hfin).toAddMonoidHom
  have hB : ∀ a, ⇑(B a) = kernelProduct hn hfin a := fun a => by simp [B]
  have h0 : Tendsto (fun p : NovikovModule R F₁ × NovikovModule R F₂ =>
      kernelProduct hn hfin p.1 p.2) (𝓝 (0, 0)) (𝓝 0) :=
    ((hasBasis_nhds_zero.prod_nhds hasBasis_nhds_zero).tendsto_iff hasBasis_nhds_zero).2
      fun D _ => ⟨((D - C) / 2, (D - C) / 2), ⟨trivial, trivial⟩, fun p hp => by
        simpa [add_halves] using kernelProduct_mem_potentialFiltration hn hfin hp.1 hp.2⟩
  simpa only [hB] using continuous_of_continuousAt_zero₂ B (by simpa [ContinuousAt, hB] using h0)
    (fun a => by simpa only [hB] using (continuous_kernelProduct_right hn hfin a).continuousAt)
    (fun b => by simpa only [hB] using (continuous_kernelProduct_left hn hfin b).continuousAt)

end KernelProduct

end NovikovModule

end TauCeti
