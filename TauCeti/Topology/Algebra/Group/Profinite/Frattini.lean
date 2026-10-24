/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Frattini
public import TauCeti.Topology.Algebra.Group.ContinuousAut.Characteristic
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex
import Mathlib.Topology.Separation.Connected
import TauCeti.Topology.Algebra.Group.Generation

/-!
# The Frattini subgroup of a profinite group

The **Frattini subgroup** `profiniteFrattini G` of a topological group `G` is the intersection of
its maximal open subgroups, written `Φ(G)`. For a profinite group this is the Frattini subgroup of
Ribes–Zalesskii. It is closed and normal, it is preserved by every continuous automorphism, and a
continuous surjection carries it into the Frattini subgroup of the target. With the discrete
topology every subgroup is open, and `profiniteFrattini G` is Mathlib's abstract `frattini G`.

The abstract Frattini subgroup is the wrong object for an infinite profinite group: a maximal
subgroup need not be open, and topological generation, not abstract generation, is what the
theory of profinite groups measures. The topological version consists of **non-generators**
in the topological sense: a closed subgroup `H` with `H ⊔ Φ(G) = G` is all of `G`. The input is
that in a compact group a proper open subgroup lies in a maximal subgroup, which is again open;
this is the finite statement for the finite quotient by an open normal subgroup inside it. A
proper closed subgroup `H` of a profinite group lies in a proper open subgroup `H ⊔ U`, for an open
normal subgroup `U`, hence in a maximal open subgroup, which also contains `Φ(G)`.

The consequence is the **lifting of generators along Frattini covers**. Let `f : G → K` be a
continuous surjection of a profinite group onto a Hausdorff group whose kernel lies in `Φ(G)`. A
set topologically generates `G` exactly when its image topologically generates `K`; in particular
every lift of a topologically generating family of `K` topologically generates `G`. Unlike
Gaschütz's lifting lemma (`TauCeti.exists_comp_eq_and_topologicalClosure_closure_range_eq_top`),
this needs no finiteness of the family, and the lift is arbitrary.

## Main definitions

* `TauCeti.profiniteFrattini`: the intersection of the maximal open subgroups.

## Main results

* `TauCeti.isTopCharacteristic_profiniteFrattini`: the Frattini subgroup is preserved by every
  continuous automorphism, and so it is normal (`TauCeti.profiniteFrattini_normal`).
* `MonoidHom.map_profiniteFrattini_le`: a continuous surjection carries the Frattini subgroup into
  the Frattini subgroup of the target.
* `TauCeti.profiniteFrattini_eq_frattini`: for a discrete group, the Frattini subgroup is Mathlib's
  `frattini`.
* `TauCeti.eq_top_of_sup_profiniteFrattini_eq_top`: the Frattini subgroup of a profinite group
  consists of non-generators.
* `TauCeti.topologicalClosure_closure_eq_top_iff_of_ker_le_profiniteFrattini`: along a continuous
  surjection with kernel in the Frattini subgroup, a set topologically generates the source exactly
  when its image topologically generates the target.
* `TauCeti.topologicalClosure_closure_range_eq_top_of_ker_le_profiniteFrattini`: every lift of a
  topologically generating family along such a map is topologically generating.
* `TauCeti.topologicalClosure_closure_eq_top_iff_quotient_profiniteFrattini`: a set topologically
  generates a profinite group exactly when its image topologically generates the quotient by the
  Frattini subgroup.

The non-generator argument generalizes the formal proofs
`TauCeti.IsProP.eq_top_of_forall_not_le_openNormalSubgroup_index_eq` and
`TauCeti.IsProP.eq_top_of_sup_proPFrattini_eq_top` in
`TauCeti.Topology.Algebra.Group.Profinite.ProP.Burnside`, replacing open normal subgroups of
index `p` by maximal open subgroups.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8.
-/

public section

namespace TauCeti

universe u v

section Defs

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- The **Frattini subgroup** `Φ(G)` of a topological group: the intersection of its maximal open
subgroups. For a profinite group this is the Frattini subgroup of Ribes–Zalesskii; with the
discrete topology it is Mathlib's `frattini` (`TauCeti.profiniteFrattini_eq_frattini`). -/
def profiniteFrattini : Subgroup G :=
  ⨅ (M : Subgroup G) (_ : IsOpen (M : Set G)) (_ : IsCoatom M), M

end Defs

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {H : Type v} [Group H] [TopologicalSpace H]

/-- The defining equation of the Frattini subgroup: the body of `TauCeti.profiniteFrattini` is
not exposed, so unfolding it goes through this lemma. -/
theorem profiniteFrattini_def :
    profiniteFrattini G = ⨅ (M : Subgroup G) (_ : IsOpen (M : Set G)) (_ : IsCoatom M), M := by
  rw [profiniteFrattini]

/-- An element lies in the Frattini subgroup exactly when it lies in every maximal open
subgroup. -/
theorem mem_profiniteFrattini_iff {x : G} :
    x ∈ profiniteFrattini G ↔ ∀ M : Subgroup G, IsOpen (M : Set G) → IsCoatom M → x ∈ M := by
  simp only [profiniteFrattini_def, Subgroup.mem_iInf]

/-- The Frattini subgroup is contained in every maximal open subgroup. -/
theorem profiniteFrattini_le {M : Subgroup G} (hMo : IsOpen (M : Set G)) (hM : IsCoatom M) :
    profiniteFrattini G ≤ M :=
  fun _ hx ↦ mem_profiniteFrattini_iff.mp hx M hMo hM

/-- The Frattini subgroup is closed whenever translations are continuous, as an intersection of
open, hence closed, subgroups. -/
instance isClosed_profiniteFrattini [SeparatelyContinuousMul G] :
    IsClosed ((profiniteFrattini G : Subgroup G) : Set G) := by
  rw [profiniteFrattini_def]
  simp only [Subgroup.coe_iInf]
  exact isClosed_iInter fun _ ↦ isClosed_iInter fun hMo ↦ isClosed_iInter fun _ ↦
    Subgroup.isClosed_of_isOpen _ hMo

/-! ### Functoriality -/

/-- A continuous surjection carries the Frattini subgroup into the Frattini subgroup of the
target: the preimage of a maximal open subgroup is again a maximal open subgroup. -/
theorem _root_.MonoidHom.profiniteFrattini_le_comap (f : G →* H) (hf : Continuous f)
    (hsurj : Function.Surjective f) : profiniteFrattini G ≤ (profiniteFrattini H).comap f :=
  fun _ hx ↦ mem_profiniteFrattini_iff.mpr fun _ hMo hM ↦
    profiniteFrattini_le (hMo.preimage hf) (Subgroup.isCoatom_comap_of_surjective hsurj hM) hx

/-- The image of the Frattini subgroup under a continuous surjection lies in the Frattini subgroup
of the target. -/
theorem _root_.MonoidHom.map_profiniteFrattini_le (f : G →* H) (hf : Continuous f)
    (hsurj : Function.Surjective f) : (profiniteFrattini G).map f ≤ profiniteFrattini H :=
  Subgroup.map_le_iff_le_comap.mpr (f.profiniteFrattini_le_comap hf hsurj)

/-- Continuous multiplicative equivalences identify the Frattini subgroups of their source and
target. -/
@[simp]
theorem _root_.ContinuousMulEquiv.map_profiniteFrattini_eq (e : G ≃ₜ* H) :
    (profiniteFrattini G).map (e : G ≃* H) = profiniteFrattini H := by
  refine le_antisymm (MonoidHom.map_profiniteFrattini_le _ e.continuous e.surjective)
    fun x hx ↦ ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  exact e.symm.toMulEquiv.toMonoidHom.map_profiniteFrattini_le e.symm.continuous
    e.symm.surjective (Subgroup.mem_map_of_mem _ hx)

/-- The Frattini subgroup is topologically characteristic: every continuous automorphism maps it
onto itself. -/
theorem isTopCharacteristic_profiniteFrattini : IsTopCharacteristic G (profiniteFrattini G) :=
  isTopCharacteristic_iff_map_eq.mpr fun φ ↦ ContinuousMulEquiv.map_profiniteFrattini_eq φ

/-- The Frattini subgroup is normal whenever translations are continuous. -/
instance profiniteFrattini_normal [SeparatelyContinuousMul G] : (profiniteFrattini G).Normal :=
  isTopCharacteristic_profiniteFrattini.normal

/-- **The Frattini subgroup of a discrete group is its abstract Frattini subgroup.** With the
discrete topology every subgroup is open, so the maximal open subgroups are all the maximal
subgroups. -/
theorem profiniteFrattini_eq_frattini [DiscreteTopology G] : profiniteFrattini G = frattini G := by
  rw [profiniteFrattini_def, frattini, Order.radical]
  simp only [isOpen_discrete, iInf_true, Set.mem_ofPred_eq]

/-! ### Non-generators -/

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **The Frattini subgroup of a profinite group consists of non-generators.** A closed subgroup
`H` with `H ⊔ Φ(G) = G` is all of `G`. -/
theorem eq_top_of_sup_profiniteFrattini_eq_top {H : Subgroup G} (hH : IsClosed (H : Set G))
    (hsup : H ⊔ profiniteFrattini G = ⊤) : H = ⊤ := by
  by_contra hHtop
  -- `H` is the intersection of the open subgroups `H ⊔ U`, `U` open normal, so one of them is
  -- proper; a maximal open subgroup above it contains both `H` and `Φ(G)`.
  obtain ⟨U, hU⟩ : ∃ U : OpenNormalSubgroup G, H ⊔ U.toSubgroup ≠ ⊤ := by
    by_contra! hall
    exact hHtop (by
      rw [H.eq_iInf_sup_openNormalSubgroup hH]
      exact top_unique (le_iInf fun U ↦ (hall U).ge))
  obtain ⟨M, hMo, hM, hHM⟩ :=
    Subgroup.exists_isOpen_isCoatom_le_of_isOpen (Subgroup.isOpen_mono le_sup_right U.isOpen) hU
  exact hM.1 (top_unique (hsup ▸ sup_le (le_sup_left.trans hHM) (profiniteFrattini_le hMo hM)))

/-- **The Frattini subgroup of a nontrivial profinite group is proper.** Otherwise the trivial
subgroup would generate together with it. -/
theorem profiniteFrattini_ne_top [Nontrivial G] : profiniteFrattini G ≠ ⊤ := fun h ↦
  (bot_ne_top : (⊥ : Subgroup G) ≠ ⊤) (eq_top_of_sup_profiniteFrattini_eq_top
    (by rw [Subgroup.coe_bot]; exact isClosed_singleton) (by rw [h, sup_top_eq]))

/-! ### Lifting generators along Frattini covers -/

variable {K : Type v} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K]

/-- **Generators lift along Frattini covers.** Let `f : G →* K` be a continuous surjection from a
profinite group onto a Hausdorff group with kernel in the Frattini subgroup of `G`. A set
topologically generates `G` if and only if its image topologically generates `K`. -/
theorem topologicalClosure_closure_eq_top_iff_of_ker_le_profiniteFrattini {f : G →* K}
    (hf : Continuous f) (hsurj : Function.Surjective f) (hker : f.ker ≤ profiniteFrattini G)
    (s : Set G) :
    (Subgroup.closure s).topologicalClosure = ⊤ ↔
      (Subgroup.closure (f '' s)).topologicalClosure = ⊤ := by
  refine ⟨fun hs ↦ topologicalClosure_closure_image_eq_top hs hf hsurj.denseRange, fun hs ↦ ?_⟩
  set L := (Subgroup.closure s).topologicalClosure
  have hLc : IsClosed (L : Set G) := Subgroup.isClosed_topologicalClosure _
  -- The image of the compact subgroup `L` is the closure of the subgroup generated by `f '' s`.
  have hLK : L.map f = ⊤ := by
    rw [f.map_topologicalClosure hf _ hLc.isCompact, MonoidHom.map_closure, hs]
  have hLker : L ⊔ f.ker = ⊤ := by rw [← Subgroup.comap_map_eq, hLK, Subgroup.comap_top]
  exact eq_top_of_sup_profiniteFrattini_eq_top hLc (top_unique (hLker ▸ sup_le_sup_left hker _))

/-- **Every lift of a generating family along a Frattini cover generates.** Let `f : G →* K` be a
continuous surjection from a profinite group onto a Hausdorff group with kernel in the Frattini
subgroup of `G`. A family `g` of elements of `G` whose image under `f` topologically generates `K`
topologically generates `G`. No finiteness of the index type is needed. -/
theorem topologicalClosure_closure_range_eq_top_of_ker_le_profiniteFrattini {f : G →* K}
    (hf : Continuous f) (hsurj : Function.Surjective f) (hker : f.ker ≤ profiniteFrattini G)
    {ι : Type*} {g : ι → G} (hg : (Subgroup.closure (Set.range (f ∘ g))).topologicalClosure = ⊤) :
    (Subgroup.closure (Set.range g)).topologicalClosure = ⊤ := by
  rw [topologicalClosure_closure_eq_top_iff_of_ker_le_profiniteFrattini hf hsurj hker,
    ← Set.range_comp]
  exact hg

/-- **Generation modulo the Frattini subgroup.** A set topologically generates a profinite
group if and only if its image topologically generates the quotient by the Frattini subgroup. -/
theorem topologicalClosure_closure_eq_top_iff_quotient_profiniteFrattini (s : Set G) :
    (Subgroup.closure s).topologicalClosure = ⊤ ↔
      (Subgroup.closure (QuotientGroup.mk' (profiniteFrattini G) '' s)).topologicalClosure =
        ⊤ :=
  topologicalClosure_closure_eq_top_iff_of_ker_le_profiniteFrattini QuotientGroup.continuous_mk
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _).le s

end TauCeti
