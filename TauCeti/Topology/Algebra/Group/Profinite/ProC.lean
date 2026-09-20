/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FiniteGroupClass
public import TauCeti.Topology.Algebra.Group.Profinite.MaximalProP

/-!
# Pro-`C` groups and the pro-`C` completion

Let `C` be a class of finite groups, in the sense of `TauCeti.FiniteGroupClass`. A topological
group is **pro-`C`** when each of its quotients by an open normal subgroup is a finite group in
`C`. The **`C`-kernel** `proCKernel C G` is the intersection of the open normal subgroups whose
quotient lies in `C`, and the **pro-`C` completion** is `proCCompletion C G = G ⧸ proCKernel C G`.
For profinite `G` this is the universal pro-`C` group receiving a continuous homomorphism
from `G`.

This is the uniform version of the construction that
`TauCeti/Topology/Algebra/Group/Profinite/MaximalProP.lean` performs for the single class of
finite `p`-groups, and the proofs run along the same lines: the substantial step is that
`proCCompletion C G` really is pro-`C`, by a compactness argument on the defining family, which
is downward directed because the normal subgroups with quotient in `C` are closed under binary
intersection. The universal property needs no compactness, only that the family is stable under
preimage.

The two constructions are cut out by different index sets, so they are compared by a theorem
rather than by unfolding: `proCKernel_finiteGroupClassP_eq_proPKernel` identifies the two
kernels for the class of finite `p`-groups, and `proCCompletion.equivMaximalProPQuotient` is
the resulting topological isomorphism of completions.

Membership is transported through `Shrink`, so the class, the groups, and the continuous
homomorphisms between them may live in independent universes.

## Main definitions

* `TauCeti.IsProC`: every quotient by an open normal subgroup is a finite group in the class.
* `TauCeti.proCKernel`: the intersection of the open normal subgroups with quotient in the
  class.
* `TauCeti.proCCompletion`: the quotient `G ⧸ proCKernel C G`.
* `TauCeti.proCCompletion.mk`: the canonical quotient homomorphism.
* `TauCeti.proCCompletion.map`: the functorial action on continuous homomorphisms.
* `TauCeti.proCCompletion.lift`: the canonical factorisation of a continuous homomorphism to a
  profinite pro-`C` group.

## Main results

* `TauCeti.isClosed_proCKernel`: the `C`-kernel is closed, so the completion is profinite again.
* `TauCeti.exists_openNormalSubgroup_memFinite_le`: an open subgroup containing the `C`-kernel
  contains a member of the defining family.
* `TauCeti.isProC_proCCompletion`: the pro-`C` completion is pro-`C`.
* `TauCeti.existsUnique_continuousMonoidHom_proCCompletion`: a continuous homomorphism from `G`
  to a profinite pro-`C` group factors uniquely and continuously through the completion.
* `TauCeti.proCKernel_eq_bot_iff`: `G` is pro-`C` exactly when its `C`-kernel is trivial; with
  `TauCeti.proCKernel_proCCompletion_eq_bot` this is idempotence of the completion.
* `TauCeti.proCKernel_finiteGroupClassP_eq_proPKernel`: for the class of finite `p`-groups the
  `C`-kernel is the pro-`p` kernel.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Sections 2.1 and 3.2.
-/

public section

namespace TauCeti

universe u v w x

section Defs

variable (C : FiniteGroupClass.{u}) (G : Type v) [Group G] [TopologicalSpace G]

/-- A topological group is **pro-`C`** when every quotient by an open normal subgroup is a
finite group in the class `C`. For a profinite group these quotients are exactly its
continuous finite quotients. -/
def IsProC : Prop :=
  ∀ U : OpenNormalSubgroup G, C.MemFinite (G ⧸ U.toSubgroup)

/-- The **`C`-kernel** of a topological group `G`: the intersection of the open normal
subgroups of `G` whose quotient lies in `C`. For profinite `G` it is the kernel of the
universal continuous homomorphism from `G` to a pro-`C` group. -/
def proCKernel : Subgroup G :=
  ⨅ U : {U : OpenNormalSubgroup G // C.MemFinite (G ⧸ U.toSubgroup)}, U.1.toSubgroup

/-- The `C`-kernel is a normal subgroup. -/
instance proCKernel_normal : (proCKernel C G).Normal :=
  Subgroup.normal_iInf_normal fun U ↦ U.1.isNormal'

/-- The **pro-`C` completion** `G ⧸ proCKernel C G`. -/
abbrev proCCompletion : Type v := G ⧸ proCKernel C G

/-- The canonical homomorphism from `G` to its pro-`C` completion. -/
abbrev proCCompletion.mk : G →* proCCompletion C G :=
  QuotientGroup.mk' (proCKernel C G)

/-- The canonical quotient homomorphism sends an element to its quotient class. -/
@[simp]
theorem proCCompletion.mk_apply (x : G) : proCCompletion.mk C G x = QuotientGroup.mk x :=
  rfl

/-- The canonical homomorphism to the pro-`C` completion is surjective. -/
theorem proCCompletion.mk_surjective : Function.Surjective (proCCompletion.mk C G) :=
  QuotientGroup.mk'_surjective (proCKernel C G)

/-- The canonical homomorphism to the pro-`C` completion is continuous. -/
theorem proCCompletion.continuous_mk : Continuous (proCCompletion.mk C G) :=
  QuotientGroup.continuous_mk

end Defs

variable {C : FiniteGroupClass.{u}} {G : Type v} {H : Type w} [Group G] [TopologicalSpace G]
variable [Group H] [TopologicalSpace H]

/-- The defining property of `IsProC`, available to modules that only see the declaration and
not its body. -/
theorem isProC_iff : IsProC C G ↔ ∀ U : OpenNormalSubgroup G, C.MemFinite (G ⧸ U.toSubgroup) :=
  Iff.rfl

/-- Membership in the `C`-kernel, unfolded over the defining family. -/
theorem mem_proCKernel_iff {x : G} :
    x ∈ proCKernel C G ↔
      ∀ U : OpenNormalSubgroup G, C.MemFinite (G ⧸ U.toSubgroup) → x ∈ U.toSubgroup := by
  rw [proCKernel, Subgroup.mem_iInf]
  exact ⟨fun h U hU ↦ h ⟨U, hU⟩, fun h U ↦ h U.1 U.2⟩

/-- The `C`-kernel is contained in every open normal subgroup whose quotient lies in `C`. -/
theorem proCKernel_le {U : OpenNormalSubgroup G} (hU : C.MemFinite (G ⧸ U.toSubgroup)) :
    proCKernel C G ≤ U.toSubgroup :=
  fun _ hx ↦ mem_proCKernel_iff.mp hx U hU

/-- The `C`-kernel is closed, so its quotient is profinite when `G` is profinite. -/
instance isClosed_proCKernel [IsTopologicalGroup G] :
    IsClosed ((proCKernel C G : Subgroup G) : Set G) := by
  rw [proCKernel, Subgroup.coe_iInf]
  exact isClosed_iInter fun U ↦ U.1.toOpenSubgroup.isClosed

/-! ### Functoriality -/

/-- A continuous homomorphism carries the `C`-kernel into the `C`-kernel. -/
theorem proCKernel_le_comap (f : G →* H) (hf : Continuous f) :
    proCKernel C G ≤ (proCKernel C H).comap f := by
  intro x hx
  rw [Subgroup.mem_comap, mem_proCKernel_iff]
  intro V hV
  exact mem_proCKernel_iff.mp hx
    ⟨V.toOpenSubgroup.comap f hf, V.isNormal'.comap f⟩ (hV.quotient_comap f)

/-- The image of the `C`-kernel under a continuous homomorphism lies in the `C`-kernel of the
target. -/
theorem map_proCKernel_le (f : G →* H) (hf : Continuous f) :
    (proCKernel C G).map f ≤ proCKernel C H :=
  Subgroup.map_le_iff_le_comap.mpr (proCKernel_le_comap f hf)

/-- Continuous multiplicative equivalences identify the `C`-kernels of their source and target.
In particular, the `C`-kernel is characteristic under continuous automorphisms. -/
theorem map_proCKernel_eq (e : G ≃ₜ* H) :
    (proCKernel C G).map e.toMulEquiv.toMonoidHom = proCKernel C H := by
  refine le_antisymm (map_proCKernel_le _ e.continuous) fun x hx ↦ ?_
  have hsymm : e.symm x ∈ proCKernel C G :=
    map_proCKernel_le e.symm.toMulEquiv.toMonoidHom e.symm.continuous
      (Subgroup.mem_map_of_mem _ hx)
  exact ⟨e.symm x, hsymm, e.apply_symm_apply x⟩

/-- The map induced on pro-`C` completions by a continuous homomorphism. -/
def proCCompletion.map (f : G →* H) (hf : Continuous f) :
    proCCompletion C G →* proCCompletion C H :=
  QuotientGroup.map (proCKernel C G) (proCKernel C H) f (proCKernel_le_comap f hf)

/-- The induced map on pro-`C` completions is computed on classes by `f`. -/
@[simp]
theorem proCCompletion.map_mk (f : G →* H) (hf : Continuous f) (x : G) :
    proCCompletion.map (C := C) f hf (x : proCCompletion C G) = proCCompletion.mk C H (f x) := by
  rfl

/-- The induced map on pro-`C` completions is continuous. -/
theorem proCCompletion.continuous_map (f : G →* H) (hf : Continuous f) :
    Continuous (proCCompletion.map (C := C) f hf) :=
  (QuotientGroup.isQuotientMap_mk (proCKernel C G)).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp hf)

/-- Functoriality: the identity induces the identity. -/
@[simp]
theorem proCCompletion.map_id :
    proCCompletion.map (C := C) (MonoidHom.id G) continuous_id = MonoidHom.id _ := by
  ext x
  rfl

/-- Functoriality: the induced maps compose. -/
@[simp]
theorem proCCompletion.map_comp {K : Type x} [Group K] [TopologicalSpace K] (f : G →* H)
    (hf : Continuous f) (g : H →* K) (hg : Continuous g) :
    proCCompletion.map (C := C) (g.comp f) (hg.comp hf) =
      (proCCompletion.map g hg).comp (proCCompletion.map f hf) := by
  ext x
  rfl

/-! ### The compactness step -/

section Compact

variable [IsTopologicalGroup G] [CompactSpace G]

/-- An open subgroup containing the `C`-kernel contains an open normal subgroup whose quotient
lies in `C`. -/
theorem exists_openNormalSubgroup_memFinite_le {M : Subgroup G} (hM : IsOpen (M : Set G))
    (hKM : proCKernel C G ≤ M) :
    ∃ U : OpenNormalSubgroup G, C.MemFinite (G ⧸ U.toSubgroup) ∧ U.toSubgroup ≤ M := by
  -- The defining family, and the closed sets it cuts out outside `M`.
  let S : Type v := {U : OpenNormalSubgroup G // C.MemFinite (G ⧸ U.toSubgroup)}
  let t : S → Set G := fun U ↦ (U.1 : Set G) \ (M : Set G)
  -- The family contains the whole group, so it is nonempty.
  have _ : Subsingleton (G ⧸ (openNormalSubgroupTop G).toSubgroup) :=
    QuotientGroup.subsingleton_iff.mpr (openNormalSubgroupTop_toSubgroup G)
  have htop : S := ⟨openNormalSubgroupTop G, FiniteGroupClass.memFinite_of_subsingleton⟩
  have hne : Nonempty S := ⟨htop⟩
  suffices h : ∃ U : S, t U = ∅ by
    obtain ⟨U, hU⟩ := h
    exact ⟨U.1, U.2, fun _ hx ↦ Set.sdiff_eq_empty.mp hU hx⟩
  by_contra hcon
  have hnonempty : ∀ U : S, (t U).Nonempty := fun U ↦ by
    rw [Set.nonempty_iff_ne_empty]
    exact fun h ↦ hcon ⟨U, h⟩
  have hclosed : ∀ U : S, IsClosed (t U) := fun U ↦ (U.1.toOpenSubgroup.isClosed).sdiff hM
  -- The family is closed under intersection, so the sets `t U` are downward directed.
  have hdirected : Directed (· ⊇ ·) t := fun U V ↦
    ⟨⟨U.1 ⊓ V.1, U.2.quotient_inf V.2⟩,
      Set.sdiff_subset_sdiff_left (SetLike.coe_subset_coe.mpr inf_le_left),
      Set.sdiff_subset_sdiff_left (SetLike.coe_subset_coe.mpr inf_le_right)⟩
  -- Cantor: their intersection is nonempty, yet it lies in `proCKernel C G \ M = ∅`.
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t
    hdirected hnonempty (fun U ↦ (hclosed U).isCompact) hclosed
  rw [Set.mem_iInter] at hx
  exact (hx htop).2 (hKM (mem_proCKernel_iff.mpr fun U hU ↦ (hx ⟨U, hU⟩).1))

/-- An open normal subgroup containing the `C`-kernel has its quotient in `C`. -/
theorem memFinite_quotient_of_proCKernel_le {U : OpenNormalSubgroup G}
    (hU : proCKernel C G ≤ U.toSubgroup) : C.MemFinite (G ⧸ U.toSubgroup) := by
  obtain ⟨V, hV, hVU⟩ := exists_openNormalSubgroup_memFinite_le U.toOpenSubgroup.isOpen hU
  have hle : V.toSubgroup ≤ (U.toSubgroup).comap (MonoidHom.id G) := by
    simpa using hVU
  refine hV.of_surjective (QuotientGroup.map V.toSubgroup U.toSubgroup (MonoidHom.id G) hle) ?_
  exact QuotientGroup.map_surjective_of_surjective V.toSubgroup U.toSubgroup (MonoidHom.id G)
    (QuotientGroup.mk'_surjective U.toSubgroup) hle

/-- For an open normal subgroup of a compact group, containing the `C`-kernel is the same as
having its quotient in `C`. -/
theorem proCKernel_le_iff_memFinite_quotient {U : OpenNormalSubgroup G} :
    proCKernel C G ≤ U.toSubgroup ↔ C.MemFinite (G ⧸ U.toSubgroup) :=
  ⟨memFinite_quotient_of_proCKernel_le, proCKernel_le⟩

/-- **The pro-`C` completion is pro-`C`.** -/
theorem isProC_proCCompletion : IsProC C (proCCompletion C G) := by
  refine isProC_iff.mpr fun M ↦ ?_
  let π : G →* proCCompletion C G := proCCompletion.mk C G
  let M' : OpenNormalSubgroup G :=
    { toOpenSubgroup := M.toOpenSubgroup.comap π QuotientGroup.continuous_mk
      isNormal' := M.isNormal'.comap π }
  let _ : M'.toSubgroup.Normal := M'.isNormal'
  have hmem : ∀ x : G, x ∈ M'.toSubgroup ↔ π x ∈ M.toSubgroup := fun _ ↦ Iff.rfl
  have hKM' : proCKernel C G ≤ M'.toSubgroup := by
    intro x hx
    rw [hmem]
    have hx1 : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hx1]
    exact one_mem _
  have hM' : C.MemFinite (G ⧸ M'.toSubgroup) := memFinite_quotient_of_proCKernel_le hKM'
  let q := (QuotientGroup.mk' M.toSubgroup).comp π
  have hq : M'.toSubgroup ≤ q.ker := fun x hx ↦
    (QuotientGroup.eq_one_iff (π x)).mpr ((hmem x).mp hx)
  refine hM'.of_surjective (QuotientGroup.lift M'.toSubgroup q hq) ?_
  exact QuotientGroup.lift_surjective_of_surjective M'.toSubgroup q
    ((QuotientGroup.mk'_surjective M.toSubgroup).comp (proCCompletion.mk_surjective C G)) hq

end Compact

/-! ### The universal property -/

section UniversalProperty

variable {P : Type w} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [TotallyDisconnectedSpace P]

/-- A continuous homomorphism to a profinite pro-`C` group kills the `C`-kernel. -/
theorem proCKernel_le_ker (hP : IsProC C P) (f : G →* P) (hf : Continuous f) :
    proCKernel C G ≤ f.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  refine Subgroup.eq_one_of_mem_iInf_openNormalSubgroup fun V ↦ ?_
  exact mem_proCKernel_iff.mp hx ⟨V.toOpenSubgroup.comap f hf, V.isNormal'.comap f⟩
    ((isProC_iff.mp hP V).quotient_comap f)

/-- The canonical factorisation of a continuous homomorphism to a profinite pro-`C` group
through the pro-`C` completion. -/
def proCCompletion.lift (hP : IsProC C P) (f : G →* P) (hf : Continuous f) :
    proCCompletion C G →* P :=
  QuotientGroup.lift (proCKernel C G) f fun _ hx ↦ proCKernel_le_ker hP f hf hx

/-- The factorisation through the pro-`C` completion computes as `f` on classes. -/
@[simp]
theorem proCCompletion.lift_mk (hP : IsProC C P) (f : G →* P) (hf : Continuous f) (x : G) :
    proCCompletion.lift hP f hf (x : proCCompletion C G) = f x := by
  rfl

/-- The factorisation through the pro-`C` completion recovers `f`. -/
@[simp]
theorem proCCompletion.lift_comp_mk (hP : IsProC C P) (f : G →* P) (hf : Continuous f) :
    (proCCompletion.lift hP f hf).comp (proCCompletion.mk C G) = f := by
  ext x
  rfl

/-- The factorisation through the pro-`C` completion is continuous. -/
theorem proCCompletion.continuous_lift (hP : IsProC C P) (f : G →* P) (hf : Continuous f) :
    Continuous (proCCompletion.lift hP f hf) :=
  (QuotientGroup.isQuotientMap_mk (proCKernel C G)).continuous_iff.mpr hf

/-- The factorisation through the pro-`C` completion is the only homomorphism restricting to
`f` along the quotient map. -/
theorem proCCompletion.lift_unique (hP : IsProC C P) (f : G →* P) (hf : Continuous f)
    {g : proCCompletion C G →* P} (hg : ∀ x : G, g (proCCompletion.mk C G x) = f x) :
    g = proCCompletion.lift hP f hf := by
  ext x
  exact hg x

/-- Naturality in the source: the factorisation of `f ∘ u` is the factorisation of `f`
precomposed with the map induced by `u`. -/
theorem proCCompletion.lift_comp_map {G' : Type x} [Group G'] [TopologicalSpace G']
    (hP : IsProC C P) (f : G →* P) (hf : Continuous f) (u : G' →* G) (hu : Continuous u) :
    (proCCompletion.lift hP f hf).comp (proCCompletion.map (C := C) u hu) =
      proCCompletion.lift hP (f.comp u) (hf.comp hu) := by
  ext x
  rfl

/-- Naturality in the target: postcomposing the factorisation of `f` with a continuous
homomorphism of profinite pro-`C` groups gives the factorisation of the composite. -/
theorem proCCompletion.comp_lift {Q : Type x} [Group Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] [CompactSpace Q] [TotallyDisconnectedSpace Q] (hP : IsProC C P)
    (hQ : IsProC C Q) (f : G →* P) (hf : Continuous f) (v : P →* Q) (hv : Continuous v) :
    v.comp (proCCompletion.lift hP f hf) = proCCompletion.lift hQ (v.comp f) (hv.comp hf) := by
  ext x
  rfl

/-- **The universal property of the pro-`C` completion.** A continuous homomorphism to a
profinite pro-`C` group factors uniquely and continuously through the canonical quotient map. -/
theorem existsUnique_continuousMonoidHom_proCCompletion (hP : IsProC C P) (f : G →* P)
    (hf : Continuous f) :
    ∃! g : proCCompletion C G →* P,
      Continuous g ∧ ∀ x : G, g (proCCompletion.mk C G x) = f x :=
  ⟨proCCompletion.lift hP f hf,
    ⟨proCCompletion.continuous_lift hP f hf, proCCompletion.lift_mk hP f hf⟩,
    fun _ hg ↦ proCCompletion.lift_unique hP f hf hg.2⟩

end UniversalProperty

/-! ### Pro-`C` groups and idempotence -/

section Idempotence

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- A profinite group is pro-`C` exactly when its `C`-kernel is trivial. -/
theorem proCKernel_eq_bot_iff : proCKernel C G = ⊥ ↔ IsProC C G := by
  refine ⟨fun h ↦ isProC_iff.mpr fun U ↦
      memFinite_quotient_of_proCKernel_le (h.trans_le bot_le), fun hG ↦ ?_⟩
  refine le_antisymm ?_ bot_le
  rw [← Subgroup.iInf_openNormalSubgroup_eq_bot (G := G)]
  exact le_iInf fun U ↦ proCKernel_le (isProC_iff.mp hG U)

/-- The `C`-kernel of a profinite pro-`C` group is trivial. -/
theorem IsProC.proCKernel_eq_bot (hG : IsProC C G) : proCKernel C G = ⊥ :=
  proCKernel_eq_bot_iff.mpr hG

/-- The canonical continuous multiplicative equivalence from the pro-`C` completion of a
profinite pro-`C` group to the group itself. -/
def proCCompletion.equivOfIsProC (hG : IsProC C G) : proCCompletion C G ≃ₜ* G :=
  ContinuousMulEquiv.mk
    ((QuotientGroup.quotientMulEquivOfEq hG.proCKernel_eq_bot).trans QuotientGroup.quotientBot)
    ((QuotientGroup.isQuotientMap_mk (proCKernel C G)).continuous_iff.mpr continuous_id)
    (proCCompletion.continuous_mk C G)

/-- The canonical equivalence from a pro-`C` group's completion sends each class to its
representative. -/
@[simp]
theorem proCCompletion.equivOfIsProC_mk (hG : IsProC C G) (x : G) :
    proCCompletion.equivOfIsProC hG (x : proCCompletion C G) = x :=
  (rfl)

/-- **Idempotence.** The `C`-kernel of a pro-`C` completion is trivial. -/
theorem proCKernel_proCCompletion_eq_bot : proCKernel C (proCCompletion C G) = ⊥ :=
  proCKernel_eq_bot_iff.mpr isProC_proCCompletion

/-- **Idempotence.** Applying the pro-`C` completion twice gives a group canonically
continuously equivalent to applying it once. -/
def proCCompletion.idempotentEquiv :
    proCCompletion C (proCCompletion C G) ≃ₜ* proCCompletion C G :=
  proCCompletion.equivOfIsProC isProC_proCCompletion

/-- The idempotence equivalence sends each class to its representative. -/
@[simp]
theorem proCCompletion.idempotentEquiv_mk (x : proCCompletion C G) :
    proCCompletion.idempotentEquiv (x : proCCompletion C (proCCompletion C G)) = x :=
  (rfl)

end Idempotence

/-! ### The class of finite `p`-groups, and the class of all finite groups -/

section Comparison

variable [IsTopologicalGroup G] [CompactSpace G] {p : ℕ}

/-- For the class of finite `p`-groups, being pro-`C` is being pro-`p`. -/
theorem isProC_finiteGroupClassP_iff : IsProC (finiteGroupClassP.{v} p) G ↔ IsProP p G := by
  rw [isProC_iff, isProP_iff]
  refine forall_congr' fun U ↦ ?_
  have : Finite (G ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.toOpenSubgroup.isOpen
  exact FiniteGroupClass.memFinite_iff.trans (finiteGroupClassP_mem_iff p _)

/-- **The `C`-kernel of the class of finite `p`-groups is the pro-`p` kernel.** The two
subgroups are cut out by different index sets: the pro-`p` kernel by the open normal subgroups
with `p`-group quotient, the `C`-kernel by those whose quotient is in addition recorded as
finite, which for a compact group is automatic. -/
theorem proCKernel_finiteGroupClassP_eq_proPKernel :
    proCKernel (finiteGroupClassP.{v} p) G = proPKernel p G := by
  refine SetLike.ext fun x ↦ ?_
  rw [mem_proCKernel_iff, mem_proPKernel_iff]
  refine forall_congr' fun U ↦ ?_
  have : Finite (G ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.toOpenSubgroup.isOpen
  rw [FiniteGroupClass.memFinite_iff, finiteGroupClassP_mem_iff]

/-- The pro-`C` completion at the class of finite `p`-groups is the maximal pro-`p` quotient. -/
def proCCompletion.equivMaximalProPQuotient (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] :
    proCCompletion (finiteGroupClassP.{u} p) G ≃ₜ* maximalProPQuotient p G :=
  ContinuousMulEquiv.mk
    (QuotientGroup.quotientMulEquivOfEq proCKernel_finiteGroupClassP_eq_proPKernel)
    ((QuotientGroup.isQuotientMap_mk (proCKernel (finiteGroupClassP.{u} p) G)).continuous_iff.mpr
      QuotientGroup.continuous_mk)
    ((QuotientGroup.isQuotientMap_mk (proPKernel p G)).continuous_iff.mpr
      QuotientGroup.continuous_mk)

/-- The comparison with the maximal pro-`p` quotient sends a class to the class of the same
element. -/
@[simp]
theorem proCCompletion.equivMaximalProPQuotient_mk (x : G) :
    proCCompletion.equivMaximalProPQuotient p G
        (x : proCCompletion (finiteGroupClassP.{v} p) G) =
      (x : maximalProPQuotient p G) :=
  (rfl)

/-- Every profinite group is pro-`C` for the class of all finite groups, so its `C`-kernel is
trivial. Its pro-`C` completion is then the group itself, by
`TauCeti.proCCompletion.equivOfIsProC`. -/
theorem proCKernel_finiteGroupClassAll_eq_bot [TotallyDisconnectedSpace G] :
    proCKernel finiteGroupClassAll.{v} G = ⊥ :=
  proCKernel_eq_bot_iff.mpr fun U ↦ by
    have : Finite (G ⧸ U.toSubgroup) :=
      Subgroup.quotient_finite_of_isOpen _ U.toOpenSubgroup.isOpen
    exact FiniteGroupClass.memFinite_iff.mpr (finiteGroupClassAll_mem _)

end Comparison

end TauCeti
