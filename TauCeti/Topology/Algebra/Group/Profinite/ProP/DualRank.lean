/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Topology.Algebra.Group.Profinite.DualRank
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.ContinuousDual
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import TauCeti.Algebra.Module.ZMod.Exponent
import TauCeti.LinearAlgebra.Basis.Basic
import TauCeti.Topology.Algebra.Group.Profinite.Section

/-!
# The generator rank of a pro-`p` group and its continuous `𝔽_p`-dual

For a profinite pro-`p` group `G` the topological generator rank is the dimension of the continuous
`𝔽_p`-dual `TauCeti.continuousZModDual p G` over `𝔽_p`. This is Burnside's basis theorem as an
identity of cardinals, with no finiteness hypothesis anywhere; the dual, and not the Frattini
quotient itself, is the correct object, because at infinite rank the Frattini quotient is a
vector space of much larger dimension than the rank — a countable product of copies of `ℤ/p` has
rank `ℵ₀` and Frattini quotient of dimension `2 ^ ℵ₀`.

One inequality holds for every profinite group and is proved without any pro-`p` hypothesis, as
`TauCeti.rank_continuousZModDual_le_topologicalGeneratorRank`.

The other inequality is the dual-basis construction, and it is where compactness and the
elementary abelian hypothesis enter. Over the Frattini quotient `W`, the common kernel of a basis
of the dual is
trivial, so by compactness the finite intersections of those kernels are a neighbourhood basis of
`1`. In particular, for each basis vector the common kernel of the *others* is not contained in its
own kernel — otherwise a finite subfamily would already be, making it a linear combination of
finitely many of the others. Choosing a point separating it from the others gives a dual basis,
which converges to `1` and generates `W` topologically. Finally a generating set of the Frattini
quotient converging to `1` lifts to `G`, which is
`TauCeti.IsProP.topologicalGeneratorRank_quotient_proPFrattini`.

## Main results

* `TauCeti.topologicalGeneratorRank_le_rank_continuousZModDual`: for a profinite `𝔽_p`-vector group
  the dimension of the continuous `𝔽_p`-dual bounds the topological generator rank from above.
* `TauCeti.IsProP.topologicalGeneratorRank_eq_rank_continuousZModDual`: **Burnside's basis theorem,
  cardinal form** — the two agree for a profinite pro-`p` group.
* `TauCeti.IsProP.exists_tendsto_cofinite_topologicallyGenerates_coord_eq`: a basis of the
  continuous `𝔽_p`-dual of a profinite pro-`p` group has a dual family in the group, which tends to
  `1` and generates topologically — a converging basis of the group.
* `TauCeti.IsProP.finrank_continuousZModDual_eq_topologicalGeneratorRankNat`: the natural-number
  form of the theorem, for a topologically finitely generated pro-`p` group.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, (3.9.1).
-/

public section

namespace TauCeti

open Filter Topology
open scoped Cardinal

universe u

variable {p : ℕ}

/-! ### Dual bases in a profinite elementary abelian group -/

section ElementaryAbelian

variable [hp : Fact p.Prime] {W : Type u} [CommGroup W] [TopologicalSpace W]
  [IsTopologicalGroup W] [CompactSpace W] [TotallyDisconnectedSpace W]
  [hW : Module (ZMod p) (Additive W)]

include hW in
private theorem proPFrattini_eq_bot_of_isModule : proPFrattini p W = ⊥ :=
  (proPFrattini_eq_bot_iff hp.out).mpr ⟨inferInstance, exponent_dvd_of_module_zmod⟩

/-- A basis of the continuous `𝔽_p`-dual separates the points of `W`: every continuous character
is a finite linear combination of the basis, and the characters cut out the pro-`p` Frattini
subgroup, which is trivial here. -/
private theorem eq_one_of_forall_basis_eq_one {ι : Type u}
    (b : Module.Basis ι (ZMod p) (continuousZModDual p W)) {w : W}
    (hw : ∀ j, Additive.toMul (b j) w = 1) : w = 1 := by
  have hev : (Module.Dual.eval (ZMod p) (Additive W) (Additive.ofMul w)).comp
      continuousZModDualToDual = 0 := by
    refine b.ext fun j ↦ ?_
    simp [Module.Dual.eval_apply, hw j]
  have hall : ∀ φ : W →ₜ* Multiplicative (ZMod p), w ∈ φ.ker := fun φ ↦ by
    have h0 : continuousZModDualToDual (Additive.ofMul φ) (Additive.ofMul w) = 0 :=
      DFunLike.congr_fun hev (Additive.ofMul φ)
    simpa using h0
  have hbot := proPFrattini_eq_bot_of_isModule (p := p) (W := W)
  rw [proPFrattini_eq_iInf_ker] at hbot
  have hmem : w ∈ ⨅ φ : W →ₜ* Multiplicative (ZMod p), φ.ker := Subgroup.mem_iInf.mpr hall
  rw [hbot] at hmem
  simpa using hmem

omit [TotallyDisconnectedSpace W] in
/-- **Dual bases exist.** Given a basis of the continuous `𝔽_p`-dual, each basis vector takes the
value `1` at some point annihilated by all the others. Were it not so, compactness would produce a
*finite* subfamily whose common kernel lies in the kernel of the given vector, making it a linear
combination of those finitely many others. -/
private theorem exists_dual_basis {ι : Type u}
    (b : Module.Basis ι (ZMod p) (continuousZModDual p W)) (i : ι) :
    ∃ w : Additive W, continuousZModDualToDual (b i) w = 1 ∧
      ∀ j, j ≠ i → continuousZModDualToDual (b j) w = 0 := by
  classical
  have hexists : ∃ w : Additive W, (∀ j, j ≠ i → continuousZModDualToDual (b j) w = 0) ∧
      continuousZModDualToDual (b i) w ≠ 0 := by
    by_contra hcon
    have hsub : ∀ w : Additive W, (∀ j, j ≠ i → continuousZModDualToDual (b j) w = 0) →
        continuousZModDualToDual (b i) w = 0 := fun w hw ↦ by
      by_contra h
      exact hcon ⟨w, hw, h⟩
    -- Compactness restricts the hypothesis to a finite set `F` of indices.
    obtain ⟨F, hF⟩ := exists_finset_iInter_ker_subset
      (fun j : {j : ι // j ≠ i} ↦ Additive.toMul (b j.1))
      ((MonoidHom.continuous_iff_isOpen_ker _).mp (Additive.toMul (b i)).continuous)
      (fun w hw ↦ continuousZModDualToDual_eq_zero_iff.mp
        (hsub (Additive.ofMul w) fun j hj ↦ continuousZModDualToDual_eq_zero_iff.mpr
          (by simpa using Set.mem_iInter.mp hw ⟨j, hj⟩)))
    -- On the finite subfamily, `b i` is a linear combination of the others.
    have hker : ⨅ j : {j : {j : ι // j ≠ i} // j ∈ F},
        LinearMap.ker (continuousZModDualToDual (b j.1.1)) ≤
          LinearMap.ker (continuousZModDualToDual (b i)) := fun w hw ↦ by
      rw [Submodule.mem_iInf] at hw
      exact continuousZModDualToDual_eq_zero_iff.mpr
        (hF (Set.mem_iInter₂.mpr fun j hj ↦ continuousZModDualToDual_eq_zero_iff.mp (hw ⟨j, hj⟩)))
    have hspan := mem_span_of_iInf_ker_le_ker hker
    set S : Set ι := (fun j : {j : ι // j ≠ i} ↦ j.1) '' (F : Set {j : ι // j ≠ i})
    have hsubset : Set.range (fun j : {j : {j : ι // j ≠ i} // j ∈ F} ↦
        continuousZModDualToDual (b j.1.1)) ⊆ continuousZModDualToDual '' (b '' S) := by
      rintro _ ⟨j, rfl⟩
      exact ⟨b j.1.1, ⟨j.1.1, ⟨j.1, j.2, rfl⟩, rfl⟩, rfl⟩
    have hmem : continuousZModDualToDual (b i) ∈
        Submodule.map continuousZModDualToDual (Submodule.span (ZMod p) (b '' S)) := by
      rw [← Submodule.span_image]
      exact Submodule.span_mono hsubset hspan
    obtain ⟨y, hy, hyeq⟩ := hmem
    exact b.linearIndependent.notMem_span_image
      (s := S) (fun ⟨j, _, hji⟩ ↦ j.2 hji) (continuousZModDualToDual_injective hyeq ▸ hy)
  obtain ⟨w, hw0, hwi⟩ := hexists
  refine ⟨(continuousZModDualToDual (b i) w)⁻¹ • w, ?_, fun j hj ↦ ?_⟩
  · rw [LinearMap.map_smul, smul_eq_mul, inv_mul_cancel₀ hwi]
  · rw [LinearMap.map_smul, hw0 j hj, smul_zero]

omit [IsTopologicalGroup W] [CompactSpace W] [TotallyDisconnectedSpace W] in
/-- The `i`-th coordinate with respect to a basis of the continuous `𝔽_p`-dual is evaluation at the
`i`-th vector of a dual basis: both are linear and they agree on the basis. -/
private theorem coord_eq_apply_dual_basis {ι : Type u}
    (b : Module.Basis ι (ZMod p) (continuousZModDual p W)) {v : ι → Additive W}
    (hv1 : ∀ i, continuousZModDualToDual (b i) (v i) = 1)
    (hv0 : ∀ i j, j ≠ i → continuousZModDualToDual (b j) (v i) = 0) (i : ι)
    (x : continuousZModDual p W) :
    b.coord i x = continuousZModDualToDual x (v i) := by
  classical
  have hEq : b.coord i =
      (Module.Dual.eval (ZMod p) (Additive W) (v i)).comp continuousZModDualToDual := by
    refine b.ext fun j ↦ ?_
    rcases eq_or_ne j i with rfl | hji
    · simp [Module.Dual.eval_apply, hv1 j, Module.Basis.coord_apply]
    · simp [Module.Dual.eval_apply, hv0 i j hji, Module.Basis.coord_apply, Ne.symm hji]
  exact DFunLike.congr_fun hEq x

/-- **A dual family of a basis of the continuous dual.** For a basis `b` of the continuous
`𝔽_p`-dual of a profinite `𝔽_p`-vector group `W` there is a family `u : ι → W` whose evaluation
functionals are the coordinate functionals of `b`, so that `b j (u i)` is `1` for `j = i` and `0`
otherwise; it tends to `1` along the cofinite filter and generates `W` topologically. -/
private theorem exists_dual_family {ι : Type u}
    (b : Module.Basis ι (ZMod p) (continuousZModDual p W)) :
    ∃ u : ι → W, Tendsto u cofinite (𝓝 1) ∧
      (Subgroup.closure (Set.range u)).topologicalClosure = ⊤ ∧
      ∀ i (x : continuousZModDual p W),
        b.coord i x = Multiplicative.toAdd (Additive.toMul x (u i)) := by
  classical
  choose v hv1 hv0 using fun i ↦ exists_dual_basis b i
  set u : ι → W := fun i ↦ Additive.toMul (v i)
  have hmem_ker : ∀ i j, j ≠ i → u i ∈ ((Additive.toMul (b j)).ker : Subgroup W) := fun i j hj ↦
    continuousZModDualToDual_eq_zero_iff.mp (hv0 i j hj)
  refine ⟨u, ?_, ?_, fun i x ↦ ?_⟩
  -- The dual family converges to `1`: away from a finite set of indices it lies in any given
  -- neighbourhood of `1`.
  · rw [tendsto_def]
    intro U hU
    obtain ⟨V, hVU, hVopen, hV1⟩ := mem_nhds_iff.mp hU
    obtain ⟨F, hF⟩ := exists_finset_iInter_ker_subset (fun j ↦ Additive.toMul (b j)) hVopen
      (fun w hw ↦ eq_one_of_forall_basis_eq_one b
        (fun j ↦ by simpa [MonoidHom.mem_ker] using Set.mem_iInter.mp hw j) ▸ hV1)
    rw [mem_cofinite]
    refine F.finite_toSet.subset fun i hi ↦ ?_
    by_contra hiF
    exact hi (hVU (hF (Set.mem_iInter₂.mpr fun j hj ↦ hmem_ker i j fun h ↦ hiF (h ▸ hj))))
  -- The dual family generates: a character killing all of it has all coordinates `0`.
  · have hProP : IsProP p W := isProP_of_module_zmod
    refine hProP.eq_top_of_forall_not_le_openNormalSubgroup_index_eq
      (Subgroup.isClosed_topologicalClosure _) fun U hU hle ↦ ?_
    obtain ⟨φ, hφ⟩ := exists_continuousMonoidHom_ker_eq hU
    have hcoord : ∀ i, b.coord i (Additive.ofMul φ) = 0 := fun i ↦ by
      rw [coord_eq_apply_dual_basis b hv1 hv0 i]
      have hmem : u i ∈ U.toSubgroup :=
        hle (Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ⟨i, rfl⟩))
      rw [← hφ] at hmem
      exact continuousZModDualToDual_eq_zero_iff.mpr (by simpa using hmem)
    have hφone : φ = 1 := by
      have h := congrArg Additive.toMul (b.forall_coord_eq_zero_iff.mp hcoord)
      rwa [toMul_ofMul, toMul_zero] at h
    have hUtop : U.toSubgroup = ⊤ := by
      rw [← hφ, hφone]
      exact Subgroup.eq_top_iff' _ |>.mpr fun x ↦ by simp [MonoidHom.mem_ker]
    exact hp.out.ne_one <| hU.symm.trans (Subgroup.index_eq_one.mpr hUtop)
  · rw [coord_eq_apply_dual_basis b hv1 hv0 i x]
    simp [u]

/-- **Burnside's basis theorem, cardinal form: the lower bound.** A profinite group whose additive
copy is an `𝔽_p`-vector space is topologically generated by a dual family of a basis of its
continuous `𝔽_p`-dual, and such a dual family converges to `1`. -/
theorem topologicalGeneratorRank_le_rank_continuousZModDual :
    topologicalGeneratorRank W ≤ Module.rank (ZMod p) (continuousZModDual p W) := by
  let b := Module.Basis.ofVectorSpace (ZMod p) (continuousZModDual p W)
  obtain ⟨u, hu, hgen, -⟩ := exists_dual_family b
  calc
    topologicalGeneratorRank W ≤ #(Set.range u : Set W) :=
      topologicalGeneratorRank_le hu.convergesToOne_range hgen
    _ ≤ #(Module.Basis.ofVectorSpaceIndex (ZMod p) (continuousZModDual p W)) := Cardinal.mk_range_le
    _ = Module.rank (ZMod p) (continuousZModDual p W) := b.mk_eq_rank''

end ElementaryAbelian

/-! ### Burnside's basis theorem in cardinal form -/

section Burnside

variable [hp : Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **Burnside's basis theorem, cardinal form.** The topological generator rank of a profinite
pro-`p` group is the dimension of its continuous `𝔽_p`-dual over `𝔽_p`. No finiteness hypothesis is
needed, and the statement is an identity of cardinals. -/
theorem IsProP.topologicalGeneratorRank_eq_rank_continuousZModDual (hG : IsProP p G) :
    topologicalGeneratorRank G = Module.rank (ZMod p) (continuousZModDual p G) := by
  refine le_antisymm ?_ rank_continuousZModDual_le_topologicalGeneratorRank
  rw [← hG.topologicalGeneratorRank_quotient_proPFrattini,
    ← (frattiniQuotientDualEquiv (p := p) (G := G)).rank_eq]
  exact topologicalGeneratorRank_le_rank_continuousZModDual

/-- **Dual families of a basis of the continuous dual of a pro-`p` group.** For a basis `b` of
the continuous `𝔽_p`-dual of a profinite pro-`p` group `G` there is a family `g : ι → G` whose
evaluation functionals are the coordinate functionals of `b`: `b j (g i)` is `1` for `j = i` and
`0` otherwise. It tends to `1` along the cofinite filter and generates `G` topologically: it is a
topological generating set converging to `1` whose members are separated by continuous characters,
the generating set of the minimal presentations of `G`. -/
theorem IsProP.exists_tendsto_cofinite_topologicallyGenerates_coord_eq (hG : IsProP p G)
    {ι : Type u} (b : Module.Basis ι (ZMod p) (continuousZModDual p G)) :
    ∃ g : ι → G, Tendsto g cofinite (𝓝 1) ∧
      (Subgroup.closure (Set.range g)).topologicalClosure = ⊤ ∧
      ∀ i (x : continuousZModDual p G),
        b.coord i x = Multiplicative.toAdd (Additive.toMul x (g i)) := by
  -- Take a dual family of the transported basis in the Frattini quotient and lift it to `G`
  -- through a continuous section of the projection sending `1` to `1`.
  set e := frattiniQuotientDualEquiv (p := p) (G := G)
  obtain ⟨u, hu, hgen, hcoord⟩ := exists_dual_family (b.map e.symm)
  obtain ⟨s, hs, hsec, hs1⟩ := exists_continuous_section (proPFrattini p G) isClosed_proPFrattini
  have hs1' : s 1 = 1 := by
    rw [← QuotientGroup.mk_one]
    exact hs1
  set g : ι → G := fun i ↦ s (u i) with hg
  have hmk : ∀ i, ((g i : G) : G ⧸ proPFrattini p G) = u i := fun i ↦ hsec (u i)
  refine ⟨g, ?_, ?_, fun i x ↦ ?_⟩
  · exact (hs1' ▸ hs.tendsto 1).comp hu
  · rw [topologicallyGenerates_iff_frattiniQuotient hG, ← Set.range_comp]
    have hcomp : ⇑(QuotientGroup.mk' (proPFrattini p G)) ∘ g = u := funext hmk
    rw [hcomp]
    exact hgen
  · -- Coordinates against `b.map e.symm` are coordinates against `b`, and evaluating a character
    -- on the Frattini quotient at the class of `g i` evaluates it on `G` at `g i`.
    have h := hcoord i (e.symm x)
    rwa [Module.Basis.coord_map_apply, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply,
      ← hmk i, frattiniQuotientDualEquiv_symm_apply_mk] at h

/-- **Burnside's basis theorem, numerical form against the dual.** For a topologically finitely
generated profinite pro-`p` group the dimension of the continuous `𝔽_p`-dual over `𝔽_p` is the
natural-number topological generator rank. -/
theorem IsProP.finrank_continuousZModDual_eq_topologicalGeneratorRankNat (hG : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) :
    Module.finrank (ZMod p) (continuousZModDual p G) = topologicalGeneratorRankNat G hfg := by
  rw [Module.finrank, ← hG.topologicalGeneratorRank_eq_rank_continuousZModDual,
    ← topologicalGeneratorRankNat_eq_topologicalGeneratorRank hfg, Cardinal.toNat_natCast]

end Burnside

end TauCeti
