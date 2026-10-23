/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.PrimeEnd.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.Separation.InvFunOn

/-!
# Transporting prime ends along maps injective on the closure

Let `U ⊆ ℂ` be a bounded open set and let `f : ℂ → ℂ` be continuous and injective on the closure
of `U`. Since `closure U` is compact, `f` is then a homeomorphism of `closure U` onto its image,
and it carries `U` onto `f '' U` and `frontier U` into `frontier (f '' U)`. Such a map carries
crosscuts of `U` to crosscuts of `f '' U` (`Path.IsCrosscut.map'`), and the domains cut off by a
sequence of cuts to the domains cut off by the image cuts. It is uniformly continuous on
`closure U`, and on a bounded set chordal and Euclidean distances are comparable, so it carries
null chains to null chains.
Equivalence of chains is preserved and reflected, so `f` induces an injective map from the prime
ends of `U` to those of `f '' U`. This map is a bijection: by invariance of domain `f '' U` is
open, and the inverse of `f` is continuous on the closure of `f '' U` and transports null chains
back.

Carathéodory's theorem supplies such a map for a bounded Jordan domain, the extension of a
Riemann map to the closed disc; see `Conformal/PrimeEnd/JordanDomain.lean`.

## Main declarations

* `TauCeti.nullChainDomain_image` -- the image of a cut-off domain is the domain cut off by the
  image cuts.
* `TauCeti.IsNullChain.image` -- null chains transport to null chains.
* `TauCeti.nullChainEquivalent_image_iff` -- equivalence of chains is preserved and reflected.
* `TauCeti.PrimeEnd.map` -- the induced map of prime ends, with `TauCeti.PrimeEnd.map_mk`.
* `TauCeti.PrimeEnd.map_injective`, `TauCeti.PrimeEnd.map_surjective`,
  `TauCeti.PrimeEnd.map_bijective` -- it is a bijection onto the prime ends of the image.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Section 2.4.
* C. Carathéodory, *Über die Begrenzung einfach zusammenhängender Gebiete*, Math. Ann. 73
  (1913).
-/

public section

noncomputable section

open Bornology Filter Function Metric Set Topology

namespace TauCeti

variable {U V : Set ℂ} {f : ℂ → ℂ} {C C' : ℕ → Set ℂ} {n : ℕ}

/-- **Images of cut-off domains.** Let `f` be continuous and injective on the closure of a bounded
set `U`, and let the cuts `C n` and `C (n + 1)` lie in that closure. Then the domain cut off by
the `n`-th image cut `f '' C n` of `f '' U` is the image of the domain cut off by `C n`. -/
theorem nullChainDomain_image (hUb : IsBounded U) (hfc : ContinuousOn f (closure U))
    (hfi : InjOn f (closure U)) (hCn : C n ⊆ closure U) (hCn' : C (n + 1) ⊆ closure U) :
    nullChainDomain (f '' U) (fun k => f '' C k) n = f '' nullChainDomain U C n := by
  have hsd : f '' (U \ C n) = f '' U \ f '' C n := by
    rw [(hfi.mono subset_closure).image_sdiff, hfi.image_inter subset_closure hCn,
      sdiff_self_inter]
  have hcc {z : ℂ} (hz : z ∈ C (n + 1)) :
      connectedComponentIn (f '' U \ f '' C n) (f z) = f '' connectedComponentIn (U \ C n) z := by
    rw [← hsd]
    exact (hUb.isCompact_closure.image_connectedComponentIn hfc hfi
      (sdiff_subset.trans subset_closure) (hCn' hz)).symm
  ext v
  rw [mem_nullChainDomain_iff]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, hv⟩
    rw [hcc hz] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    exact mem_image_of_mem f (mem_nullChainDomain_iff.mpr ⟨z, hz, hu⟩)
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨z, hz, hu⟩ := mem_nullChainDomain_iff.mp hu
    exact ⟨f z, mem_image_of_mem f hz, hcc hz ▸ mem_image_of_mem f hu⟩

/-- **Null chains transport along maps injective on the closure.** If `f` is continuous and
injective on the closure of a bounded open set `U`, the images of the crosscuts of a null chain of
`U` form a null chain of `f '' U`. -/
theorem IsNullChain.image (hC : IsNullChain U C) (hUb : IsBounded U) (hUo : IsOpen U)
    (hfc : ContinuousOn f (closure U)) (hfi : InjOn f (closure U)) :
    IsNullChain (f '' U) fun n => f '' C n where
  exists_isCrosscut n := by
    obtain ⟨x, y, γ, hγ, hrange⟩ := hC.exists_isCrosscut n
    exact ⟨f x, f y, _, hγ.map' hUo hfc hfi, by rw [Path.map'_coe, range_comp, hrange]⟩
  disjoint_succ n :=
    (hC.disjoint_succ n).image hfi (hC.subset_closure n) (hC.subset_closure (n + 1))
  nullChainDomain_succ_subset n := by
    rw [nullChainDomain_image hUb hfc hfi (hC.subset_closure _) (hC.subset_closure _),
      nullChainDomain_image hUb hfc hfi (hC.subset_closure _) (hC.subset_closure _)]
    exact image_mono (hC.nullChainDomain_succ_subset n)
  eventually_chordal_lt ε hε := by
    -- Small chordal diameter in the bounded set `closure U` forces small Euclidean diameter, which
    -- uniform continuity of `f` on the compact set `closure U` carries to the image.
    obtain ⟨R, -, hR⟩ := hUb.closure.exists_pos_norm_le
    obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuousOn_iff.mp
      (hUb.isCompact_closure.uniformContinuousOn_of_continuous hfc) ε hε
    filter_upwards [hC.eventually_chordal_lt (δ / (1 + R ^ 2)) (by positivity)] with n hn
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    have hzU := hC.subset_closure n hz
    have hwU := hC.subset_closure n hw
    have hzw : dist z w < δ := by
      rw [dist_eq_norm]
      calc ‖z - w‖ ≤ (1 + R ^ 2) * (‖z - w‖ / √((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2))) :=
            norm_sub_le_mul_chordal (hR z hzU) (hR w hwU)
        _ < (1 + R ^ 2) * (δ / (1 + R ^ 2)) :=
            mul_lt_mul_of_pos_left (hn z hz w hw) (by positivity)
        _ = δ := mul_div_cancel₀ _ (by positivity)
    have hfzw := hfδ z hzU w hwU hzw
    rw [dist_eq_norm] at hfzw
    exact (chordal_le_norm_sub _ _).trans_lt hfzw

/-- **Equivalence of chains transports both ways.** If `f` is continuous and injective on the
closure of a bounded set `U`, two sequences of cuts in that closure are equivalent exactly when
their images are equivalent sequences of cuts of `f '' U`. -/
theorem nullChainEquivalent_image_iff (hUb : IsBounded U) (hfc : ContinuousOn f (closure U))
    (hfi : InjOn f (closure U)) (hC : ∀ n, C n ⊆ closure U) (hC' : ∀ n, C' n ⊆ closure U) :
    NullChainEquivalent (f '' U) (fun n => f '' C n) (fun n => f '' C' n) ↔
      NullChainEquivalent U C C' := by
  have hD (C : ℕ → Set ℂ) (n : ℕ) : nullChainDomain U C n ⊆ closure U :=
    nullChainDomain_subset.trans (sdiff_subset.trans subset_closure)
  have himage {C : ℕ → Set ℂ} (hC : ∀ n, C n ⊆ closure U) (n : ℕ) :
      nullChainDomain (f '' U) (fun k => f '' C k) n = f '' nullChainDomain U C n :=
    nullChainDomain_image hUb hfc hfi (hC n) (hC (n + 1))
  simp only [nullChainEquivalent_def, himage hC, himage hC',
    hfi.image_subset_image_iff (hD _ _) (hD _ _)]

namespace PrimeEnd

/-- **The map of prime ends induced by a map injective on the closure.** If `f` is continuous and
injective on the closure of a bounded open set `U`, and `f '' U = V`, the prime end of a null
chain of `U` goes to the prime end of the image chain of `V`. -/
def map (hUb : IsBounded U) (hUo : IsOpen U) (hfc : ContinuousOn f (closure U))
    (hfi : InjOn f (closure U)) (hV : f '' U = V) : PrimeEnd U → PrimeEnd V :=
  lift (fun C hC => mk (fun n => f '' C n) (hV ▸ hC.image hUb hUo hfc hfi))
    fun _ _ hC hC' h => by
      subst hV
      exact mk_eq_mk_iff.mpr ((nullChainEquivalent_image_iff hUb hfc hfi hC.subset_closure
        hC'.subset_closure).mpr h)

variable {hUb : IsBounded U} {hUo : IsOpen U} {hfc : ContinuousOn f (closure U)}
  {hfi : InjOn f (closure U)} {hV : f '' U = V}

/-- The induced map sends the prime end of a null chain to the prime end of its image chain. -/
@[simp]
theorem map_mk (hC : IsNullChain U C) :
    map hUb hUo hfc hfi hV (mk C hC) =
      mk (fun n => f '' C n) (hV ▸ hC.image hUb hUo hfc hfi) :=
  lift_mk _ _ C hC

/-- **The induced map of prime ends is injective.** -/
theorem map_injective : Injective (map hUb hUo hfc hfi hV) := by
  intro p q hpq
  induction p using PrimeEnd.ind with
  | h C hC =>
    induction q using PrimeEnd.ind with
    | h C' hC' =>
      subst hV
      rw [map_mk, map_mk, mk_eq_mk_iff] at hpq
      exact mk_eq_mk_iff.mpr ((nullChainEquivalent_image_iff hUb hfc hfi hC.subset_closure
        hC'.subset_closure).mp hpq)

/-- **The induced map of prime ends is surjective.** Every null chain of `V = f '' U` is the image
of a null chain of `U`. -/
theorem map_surjective : Surjective (map hUb hUo hfc hfi hV) := by
  subst hV
  -- By invariance of domain `f '' U` is open; the inverse of `f` transports chains back to `U`.
  have hVo : IsOpen (f '' U) :=
    hUo.image_of_continuousOn_of_injOn (E := ℂ) (F := ℂ) (hfc.mono subset_closure)
      (hfi.mono subset_closure) rfl
  intro p
  induction p using PrimeEnd.ind with
  | h D hD =>
    have hK : IsCompact (closure U) := hUb.isCompact_closure
    set g := invFunOn f (closure U)
    have hcl := image_closure_of_isCompact hK hfc
    have hgc : ContinuousOn g (closure (f '' U)) :=
      hcl ▸ hfc.continuousOn_invFunOn_image_of_isCompact hK subset_rfl hfi (by simp)
    have hgi : InjOn g (closure (f '' U)) := hcl ▸ invFunOn_injOn_image f (closure U)
    have hgU : g '' (f '' U) = U := hfi.leftInvOn_invFunOn.image_image' subset_closure
    have hVb : IsBounded (f '' U) :=
      (hK.image_of_continuousOn hfc).isBounded.subset (image_mono subset_closure)
    refine ⟨mk (fun n => g '' D n) (hgU ▸ hD.image hVb hVo hgc hgi), ?_⟩
    rw [map_mk, mk_eq_mk_iff]
    -- `f` undoes `g` on the closure of `f '' U`, where the crosscuts of `D` lie.
    have hfg (n : ℕ) : f '' (g '' D n) = D n :=
      ((surjOn_image f (closure U)).rightInvOn_invFunOn.mono
        (hcl ▸ hD.subset_closure n)).image_image
    simp only [hfg]
    exact NullChainEquivalent.refl _ _

/-- **The induced map of prime ends is a bijection.** -/
theorem map_bijective : Bijective (map hUb hUo hfc hfi hV) :=
  ⟨map_injective, map_surjective⟩

end PrimeEnd

end TauCeti

end
