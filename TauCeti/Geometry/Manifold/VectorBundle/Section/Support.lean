/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Topology.Sets.Compacts

/-!
# Compactly supported smooth bundle sections

The support of a bundle section is the closure of its nonzero locus, not the support of its
map into the total space: the zero vector varies with the base point. We define this closed
support on native `ContMDiffSection`, the submodules of sections supported in a prescribed set,
and their compactly supported submodule. The latter is the directed supremum of the
fixed-compact stages. These are algebraic carriers; no topology on section spaces is installed
here.

Smooth scalar multiplication preserves support and compact support. A compactly supported
scalar function localizes even a section without compact support, and a cutoff equal to one
on the support acts as the identity. These operations provide the support stages and
localizations used in test sections and their inductive-limit topologies.

The smoothness of multiplication is supplied by Mathlib's `ContMDiff.smul_section`.
-/

public section

open Set Bundle TopologicalSpace
open scoped Manifold ContDiff

namespace ContMDiffSection

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞ω} {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]

section Support

variable [∀ x, Zero (V x)]

/-- The closed support of a section: the closure of its nonzero locus in the base. -/
def tsupport (s : Cₛ^n⟮I; F, V⟯) : Set M := closure {x | s x ≠ 0}

/-- The closed support is the closure of the fibrewise nonzero locus. -/
theorem tsupport_def (s : Cₛ^n⟮I; F, V⟯) : s.tsupport = closure {x | s x ≠ 0} := (rfl)

/-- The closed support is closed in the base. -/
theorem isClosed_tsupport (s : Cₛ^n⟮I; F, V⟯) : IsClosed s.tsupport :=
  isClosed_closure

/-- A section vanishes off its closed support. -/
theorem eq_zero_of_notMem_tsupport (s : Cₛ^n⟮I; F, V⟯) {x : M}
    (hx : x ∉ s.tsupport) : s x = 0 := by
  by_contra h
  exact hx (subset_closure h)

/-- Containment of closed support in a closed set is equivalent to vanishing outside it. -/
theorem tsupport_subset_iff {s : Cₛ^n⟮I; F, V⟯} {K : Set M} (hK : IsClosed K) :
    s.tsupport ⊆ K ↔ ∀ x ∉ K, s x = 0 := by
  refine ⟨fun h x hx => s.eq_zero_of_notMem_tsupport (fun hs => hx (h hs)), ?_⟩
  intro h
  exact closure_minimal (fun x hx => by by_contra hxK; exact hx (h x hxK)) hK

end Support

variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

@[simp]
theorem tsupport_zero : (0 : Cₛ^n⟮I; F, V⟯).tsupport = ∅ := by
  simp [tsupport]

@[simp]
theorem tsupport_eq_empty_iff {s : Cₛ^n⟮I; F, V⟯} : s.tsupport = ∅ ↔ s = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ tsupport_zero⟩
  ext x
  exact s.eq_zero_of_notMem_tsupport (by simp [h])

/-- Addition cannot enlarge support beyond the union of the two supports. -/
theorem tsupport_add_subset (s t : Cₛ^n⟮I; F, V⟯) :
    (s + t).tsupport ⊆ s.tsupport ∪ t.tsupport := by
  apply (tsupport_subset_iff (s.isClosed_tsupport.union t.isClosed_tsupport)).2
  intro x hx
  simp only [mem_union, not_or] at hx
  simp [s.eq_zero_of_notMem_tsupport hx.1, t.eq_zero_of_notMem_tsupport hx.2]

/-- Constant scalar multiplication does not enlarge support. -/
theorem tsupport_smul_subset (c : 𝕜) (s : Cₛ^n⟮I; F, V⟯) :
    (c • s).tsupport ⊆ s.tsupport := by
  apply (tsupport_subset_iff s.isClosed_tsupport).2
  intro x hx
  simp [s.eq_zero_of_notMem_tsupport hx]

/-- Multiplication by a nonzero scalar preserves closed support. -/
theorem tsupport_smul (c : 𝕜) (s : Cₛ^n⟮I; F, V⟯) (hc : c ≠ 0) :
    (c • s).tsupport = s.tsupport := by
  refine (tsupport_smul_subset c s).antisymm ?_
  have h := tsupport_smul_subset c⁻¹ (c • s)
  simpa [smul_smul, hc] using h

variable (I F n V) in
/-- The submodule of native smooth sections whose closed support lies in `K`. -/
def supportedIn (K : Set M) : Submodule 𝕜 Cₛ^n⟮I; F, V⟯ where
  carrier := {s | s.tsupport ⊆ K}
  zero_mem' := by simp
  add_mem' := fun hs ht => (tsupport_add_subset _ _).trans (union_subset hs ht)
  smul_mem' := fun c _ hs => (tsupport_smul_subset c _).trans hs

@[simp]
theorem mem_supportedIn {K : Set M} {s : Cₛ^n⟮I; F, V⟯} :
    s ∈ supportedIn I F n V K ↔ s.tsupport ⊆ K := Iff.rfl

/-- The fixed-support stages increase with the supporting set. -/
theorem supportedIn_mono {K L : Set M} (h : K ⊆ L) :
    supportedIn I F n V K ≤ supportedIn I F n V L := fun _ hs => hs.trans h

@[simp]
theorem supportedIn_empty : supportedIn I F n V ∅ = ⊥ := by
  ext s
  simp [subset_empty_iff]

@[simp]
theorem supportedIn_univ : supportedIn I F n V univ = ⊤ := by
  ext s
  simp

@[simp]
theorem supportedIn_inter (K L : Set M) :
    supportedIn I F n V (K ∩ L) = supportedIn I F n V K ⊓ supportedIn I F n V L := by
  ext s
  simp [subset_inter_iff]

variable (I F n V) in
/-- The submodule of native smooth sections with compact closed support. Its subtype is the
algebraic compact-test carrier, before a test-space topology is chosen. -/
def compactlySupported : Submodule 𝕜 Cₛ^n⟮I; F, V⟯ where
  carrier := {s | IsCompact s.tsupport}
  zero_mem' := by simp
  add_mem' := fun hs ht => (hs.union ht).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_add_subset _ _)
  smul_mem' := fun c _ hs => hs.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_smul_subset c _)

@[simp]
theorem mem_compactlySupported {s : Cₛ^n⟮I; F, V⟯} :
    s ∈ compactlySupported I F n V ↔ IsCompact s.tsupport := Iff.rfl

/-- A section supported in a compact set has compact support. -/
theorem supportedIn_le_compactlySupported {K : Set M} (hK : IsCompact K) :
    supportedIn I F n V K ≤ compactlySupported I F n V :=
  fun s hs => hK.of_isClosed_subset s.isClosed_tsupport hs

/-- Every compactly supported section belongs to a fixed-compact stage. -/
theorem mem_compactlySupported_iff {s : Cₛ^n⟮I; F, V⟯} :
    s ∈ compactlySupported I F n V ↔
      ∃ K : Compacts M, s ∈ supportedIn I F n V K := by
  refine ⟨fun hs => ⟨⟨s.tsupport, hs⟩, Subset.rfl⟩, ?_⟩
  rintro ⟨K, hK⟩
  exact supportedIn_le_compactlySupported K.isCompact hK

/-- Fixed-compact support stages form a directed family, using union of compact sets. -/
theorem directed_supportedIn :
    Directed (· ≤ ·) (fun K : Compacts M => supportedIn I F n V K) := by
  intro K L
  exact ⟨K ⊔ L, supportedIn_mono (by exact subset_union_left),
    supportedIn_mono (by exact subset_union_right)⟩

/-- The compactly supported submodule is exactly the supremum of its fixed-compact stages.
This is an algebraic statement, not an assertion about a final topology. -/
theorem iSup_supportedIn :
    (⨆ K : Compacts M, supportedIn I F n V K) = compactlySupported I F n V := by
  apply le_antisymm
  · exact iSup_le fun K => supportedIn_le_compactlySupported K.isCompact
  · intro s hs
    obtain ⟨K, hK⟩ := mem_compactlySupported_iff.1 hs
    exact le_iSup (fun K : Compacts M => supportedIn I F n V K) K hK

/-- On a compact base every smooth section has compact support. -/
@[simp]
theorem compactlySupported_eq_top [CompactSpace M] : compactlySupported I F n V = ⊤ := by
  apply top_unique
  intro s _
  exact s.isClosed_tsupport.isCompact

/-- Multiplication of sections by a smooth scalar function as a linear map. -/
def smulLinearMap (f : C^n⟮I, M; 𝕜⟯) : Cₛ^n⟮I; F, V⟯ →ₗ[𝕜] Cₛ^n⟮I; F, V⟯ where
  toFun s := ⟨fun x => f x • s x, f.contMDiff.smul_section s.contMDiff⟩
  map_add' s t := by ext x; simp [smul_add]
  map_smul' c s := by ext x; simp [smul_smul, mul_comm]

@[simp]
theorem smulLinearMap_apply (f : C^n⟮I, M; 𝕜⟯) (s : Cₛ^n⟮I; F, V⟯) (x : M) :
    smulLinearMap f s x = f x • s x := (rfl)

/-- Scalar localization is supported in both the scalar support and the section support. -/
theorem tsupport_smulLinearMap_subset (f : C^n⟮I, M; 𝕜⟯) (s : Cₛ^n⟮I; F, V⟯) :
    (smulLinearMap f s).tsupport ⊆ _root_.tsupport f ∩ s.tsupport := by
  apply (tsupport_subset_iff ((_root_.isClosed_tsupport f).inter s.isClosed_tsupport)).2
  intro x hx
  by_cases hf : x ∈ _root_.tsupport f
  · have hs : x ∉ s.tsupport := fun hs => hx ⟨hf, hs⟩
    simp [s.eq_zero_of_notMem_tsupport hs]
  · simp [_root_.image_eq_zero_of_notMem_tsupport hf]

/-- Smooth multiplication preserves each fixed-support stage. -/
theorem smulLinearMap_mem_supportedIn (f : C^n⟮I, M; 𝕜⟯) {s : Cₛ^n⟮I; F, V⟯}
    {K : Set M} (hs : s ∈ supportedIn I F n V K) :
    smulLinearMap f s ∈ supportedIn I F n V K :=
  (tsupport_smulLinearMap_subset f s).trans (inter_subset_right.trans hs)

/-- Smooth multiplication preserves compact support of the section. -/
theorem smulLinearMap_mem_compactlySupported (f : C^n⟮I, M; 𝕜⟯) {s : Cₛ^n⟮I; F, V⟯}
    (hs : s ∈ compactlySupported I F n V) :
    smulLinearMap f s ∈ compactlySupported I F n V :=
  hs.of_isClosed_subset (isClosed_tsupport _) ((tsupport_smulLinearMap_subset f s).trans
    inter_subset_right)

/-- A compactly supported smooth scalar function localizes any smooth section to compact
support, even when the original section is not compactly supported. -/
theorem smulLinearMap_mem_compactlySupported_of_hasCompactSupport (f : C^n⟮I, M; 𝕜⟯)
    (hf : HasCompactSupport f) (s : Cₛ^n⟮I; F, V⟯) :
    smulLinearMap f s ∈ compactlySupported I F n V :=
  hf.of_isClosed_subset (isClosed_tsupport _) ((tsupport_smulLinearMap_subset f s).trans
    inter_subset_left)

/-- A cutoff equal to one on a section's closed support leaves that section unchanged. -/
theorem smulLinearMap_eq_self (f : C^n⟮I, M; 𝕜⟯) (s : Cₛ^n⟮I; F, V⟯)
    (hf : EqOn f 1 s.tsupport) : smulLinearMap f s = s := by
  ext x
  by_cases hx : x ∈ s.tsupport
  · simp [hf hx]
  · simp [s.eq_zero_of_notMem_tsupport hx]

end ContMDiffSection
