/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Coadjoint.Height
public import TauCeti.Algebra.Lie.InvariantForm.Positive
public import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Algebra.Lie.Solvable.Basic

/-!
# The centre, the roots and the coroots of a root-plane decomposition

Let `L = t + E₁ + ⋯ + E_r` be a root-plane decomposition
(`TauCeti.IsRootPlaneDecomposition B t α E J`) of a Lie algebra over a field: `t` is abelian,
the planes `E_i` are pairwise `B`-orthogonal, `B` is positive on each of them, and every `H ∈ t`
acts on `E_i` by `ad H = α_i(H) J_i` for a root `α_i ∈ t*` and a `B`-skew complex structure `J_i`.
This is the real root decomposition of the Lie algebra of a compact Lie group with respect to a
maximal torus (`TauCeti.Lie.IsMaximalTorus.exists_isRootPlaneDecomposition`). This file shows how
the roots see the centre `𝔷` of `L`, and splits `t` into the centre and a semisimple part spanned by
the coroot directions.

* **The torus is its own centralizer.** If every root is nonzero, an element commuting with every
  `H ∈ t` lies in `t` (`TauCeti.IsRootPlaneDecomposition.mem_of_forall_lie_eq_zero`): its component
  `a_i` in `E_i` satisfies `α_i(H) B(a_i, a_i) = 0`. In particular the centre lies in `t`
  (`TauCeti.IsRootPlaneDecomposition.center_le`).
* **The roots vanish exactly on the centre.** An element `H ∈ t` commuting with every plane is
  central (`TauCeti.IsRootPlaneDecomposition.mem_center_of_forall_lie_eq_zero`), and so is one
  killed by every root (`TauCeti.IsRootPlaneDecomposition.mem_center_of_forall_apply_eq_zero`).
  Conversely, for nonzero planes, `H ∈ t` is central exactly when `α_i(H) = 0` for every `i`
  (`TauCeti.IsRootPlaneDecomposition.mem_center_iff`). So the common
  kernel of the roots is `𝔷 ∩ t`
  (`TauCeti.IsRootPlaneDecomposition.dualCoannihilator_span_range`), and in finite dimensions the
  roots span the annihilator of the centre in `t*`
  (`TauCeti.IsRootPlaneDecomposition.span_range_eq_dualAnnihilator`).

Now let `B` be reflexive, invariant and anisotropic on all of `L`, as an `Ad`-invariant inner
product on the Lie algebra of a compact Lie group is, and let `L` be finite-dimensional. Then `L`
is the direct sum of its centre and its derived algebra `[L, L]`
(`LinearMap.BilinForm.isCompl_center_derivedSeries_one_of_anisotropic`), and with nonzero roots
this splitting restricts to

`t = 𝔷 ⊕ t_ss`,  `t_ss = t ∩ [L, L]`

(`TauCeti.IsRootPlaneDecomposition.isCompl_comap_center_comap_derivedSeries`).

* **The roots span the dual of `t_ss`.** The restrictions of the roots to
  `t_ss` span `t_ss*` (`TauCeti.IsRootPlaneDecomposition.span_range_domRestrict_eq_top`): no
  nonzero vector of `t_ss` is killed by all of them.
* **The coroot directions span `t_ss`.** For `v ∈ E_i` the bracket `⁅v, J_i v⁆` lies in
  `t ∩ [L, L]`, and an invariant form pairs `H ∈ t` with it to `α_i(H) B(J_i v, J_i v)`. A vector
  of `t` orthogonal to all of them is therefore central, and the brackets span `t_ss`
  (`TauCeti.IsRootPlaneDecomposition.span_lie_eq_inf_derivedSeries`). The pairing identity is
  `LinearMap.BilinForm.lieInvariant.apply_lie_eq_mul_of_lie_eq_smul`; when `B` is positive
  definite and `v ≠ 0`, also `α_i(⁅v, J_i v⁆) > 0`
  (`LinearMap.BilinForm.lieInvariant.root_apply_lie_pos_of_lie_eq_smul`).

For the Lie algebra `𝔲(n)` of the unitary group, with `t` the diagonal matrices, the roots
`e_j - e_k` vanish on the centre `iℝ · 1`, and `t_ss` is the space of traceless diagonal matrices,
spanned by the coroot directions `i (E_jj - E_kk)`.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter V, § 1 and § 2.
-/

public section

open Module (Dual)
open LieAlgebra

namespace TauCeti.IsRootPlaneDecomposition

variable {K L ι : Type*} [Field K] [PartialOrder K] [LieRing L] [LieAlgebra K L]
  {B : LinearMap.BilinForm K L} {t : Submodule K L} {α : ι → Dual K t} {E : ι → Submodule K L}
  {J : ∀ i, Module.End K (E i)}

/-! ### The centralizer of the torus and the centre -/

/-- Pairing `Σ_i ⁅H, a_i⁆` with `J_j a_j` isolates the component in `E_j`:
the result is `α_j(H) B(a_j, a_j)`. -/
private theorem apply_sum_lie_apply [Fintype ι] (hD : IsRootPlaneDecomposition B t α E J)
    (H : t) (a : ∀ i, E i) (j : ι) :
    B (∑ i, ⁅(H : L), (a i : L)⁆) (J j (a j)) = α j H * B (a j) (a j) := by
  classical
  rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single j]
  · rw [(hD.isRootPlane j).lie_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      (hD.isRootPlane j).apply_map_map]
  · intro i _ hij
    rw [(hD.isRootPlane i).lie_apply, map_smul, LinearMap.smul_apply,
      hD.apply_eq_zero hij (J i (a i)).property (J j (a j)).property, smul_zero]
  · simp

/-- **The torus of a root-plane decomposition is its own centralizer.** If every root is nonzero,
an element commuting with every `H ∈ t` lies in `t`. -/
theorem mem_of_forall_lie_eq_zero [Finite ι] (hD : IsRootPlaneDecomposition B t α E J)
    (hα : ∀ i, α i ≠ 0) {z : L} (hz : ∀ H : t, ⁅(H : L), z⁆ = 0) : z ∈ t := by
  have := Fintype.ofFinite ι
  obtain ⟨H, hH, a, rfl⟩ := hD.exists_eq_add_sum z
  -- Each component `a_j` vanishes: pairing `⁅H₀, z⁆ = 0` with `J_j a_j` gives
  -- `α_j(H₀) B(a_j, a_j) = 0` for some `H₀` with `α_j(H₀) ≠ 0`.
  have ha (j : ι) : (a j : L) = 0 := by
    obtain ⟨H₀, hH₀⟩ : ∃ H₀, α j H₀ ≠ 0 := by simpa using DFunLike.ne_iff.mp (hα j)
    have h0 := hz H₀
    rw [lie_add, hD.lie_eq_zero H₀.property hH, zero_add] at h0
    have hpair := hD.apply_sum_lie_apply H₀ a j
    rw [← lie_sum, h0, map_zero, LinearMap.zero_apply, eq_comm] at hpair
    exact hD.eq_zero_of_apply_self_eq_zero (a j).property
      ((mul_eq_zero.mp hpair).resolve_left hH₀)
  simpa [ha] using hH

/-- **The centre lies in the torus.** If every root of a root-plane decomposition is nonzero, the
centre of the Lie algebra lies in `t`. -/
theorem center_le [Finite ι] (hD : IsRootPlaneDecomposition B t α E J) (hα : ∀ i, α i ≠ 0) :
    (center K L).toSubmodule ≤ t := fun z hz ↦
  hD.mem_of_forall_lie_eq_zero hα fun H ↦
    (LieModule.mem_maxTrivSubmodule K L L z).mp hz H

/-- **An element of the torus commuting with every plane is central.** In a root-plane
decomposition, an element `H ∈ t` with `⁅H, v⁆ = 0` for every `v` in every plane `E_i` is
central. -/
theorem mem_center_of_forall_lie_eq_zero [Finite ι] (hD : IsRootPlaneDecomposition B t α E J)
    {H : t} (h : ∀ i (v : E i), ⁅(H : L), (v : L)⁆ = 0) : (H : L) ∈ center K L := by
  have := Fintype.ofFinite ι
  rw [← self_module_ker_eq_center, LieModule.mem_ker]
  intro x
  obtain ⟨H', hH', a, rfl⟩ := hD.exists_eq_add_sum x
  rw [lie_add, hD.lie_eq_zero H.property hH', zero_add, lie_sum]
  exact Finset.sum_eq_zero fun i _ ↦ h i (a i)

/-- **An element of the torus killed by every root is central.** In a root-plane decomposition,
an element `H ∈ t` with `α_i(H) = 0` for every root `α_i` is central. -/
theorem mem_center_of_forall_apply_eq_zero [Finite ι] (hD : IsRootPlaneDecomposition B t α E J)
    {H : t} (h : ∀ i, α i H = 0) : (H : L) ∈ center K L :=
  hD.mem_center_of_forall_lie_eq_zero fun i v ↦
    ((hD.isRootPlane i).lie_eq_zero_iff H v).mpr (Or.inl (h i))

/-- **The roots vanish exactly on the centre.** In a root-plane decomposition with nonzero planes,
an element `H ∈ t` is central exactly when every root vanishes at `H`. -/
theorem mem_center_iff [Finite ι] (hD : IsRootPlaneDecomposition B t α E J)
    (hE : ∀ i, E i ≠ ⊥) (H : t) : (H : L) ∈ center K L ↔ ∀ i, α i H = 0 := by
  refine ⟨fun h i ↦ ?_, hD.mem_center_of_forall_apply_eq_zero⟩
  rw [← self_module_ker_eq_center, LieModule.mem_ker] at h
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hE i)
  exact ((hD.isRootPlane i).lie_eq_zero_iff H ⟨v, hv⟩ |>.mp (h v)).resolve_right
    fun h0 ↦ hv0 (congrArg Subtype.val h0)

/-- **The common kernel of the roots is the centre.** In a root-plane decomposition with nonzero
planes, the elements of `t` killed by every root are exactly the central ones. -/
theorem dualCoannihilator_span_range [Finite ι] (hD : IsRootPlaneDecomposition B t α E J)
    (hE : ∀ i, E i ≠ ⊥) :
    (Submodule.span K (Set.range α)).dualCoannihilator =
      (center K L).toSubmodule.comap t.subtype := by
  ext H
  rw [← SetLike.mem_coe, Submodule.coe_dualCoannihilator_span]
  simp [hD.mem_center_iff hE]

/-- **The roots span the annihilator of the centre.** In a finite-dimensional Lie algebra with a
root-plane decomposition with nonzero planes, the roots span the linear forms on `t` vanishing on
the central elements of `t`. -/
theorem span_range_eq_dualAnnihilator [Finite ι] [FiniteDimensional K L]
    (hD : IsRootPlaneDecomposition B t α E J) (hE : ∀ i, E i ≠ ⊥) :
    Submodule.span K (Set.range α) =
      ((center K L).toSubmodule.comap t.subtype).dualAnnihilator := by
  rw [← hD.dualCoannihilator_span_range hE, Subspace.dualCoannihilator_dualAnnihilator_eq]

/-! ### The semisimple part of the torus -/

variable [FiniteDimensional K L]

/-- **The torus splits into the centre and a semisimple part.** For a reflexive invariant form
with anisotropic diagonal and a root-plane decomposition with nonzero roots, `t` is the direct sum
of the centre `𝔷` and its part `t ∩ [L, L]` in the derived algebra. -/
theorem isCompl_comap_center_comap_derivedSeries [Finite ι]
    (hD : IsRootPlaneDecomposition B t α E J) (hα : ∀ i, α i ≠ 0) (hrefl : B.IsRefl)
    (hani : B.toQuadraticMap.Anisotropic) (hinv : B.lieInvariant L) :
    IsCompl ((center K L).toSubmodule.comap t.subtype)
      ((derivedSeries K L 1).toSubmodule.comap t.subtype) :=
  Submodule.isCompl_comap_subtype_of_isCompl_of_le
    (LieSubmodule.isCompl_toSubmodule.mpr
      (B.isCompl_center_derivedSeries_one_of_anisotropic hrefl hani hinv))
    (hD.center_le hα)

/-- **The roots span the dual of the semisimple part of the torus.** For a reflexive invariant
form with anisotropic diagonal and a root-plane decomposition, the restrictions of the roots to
`t ∩ [L, L]` span its dual: a vector of `t ∩ [L, L]` killed by every root is central, hence
zero. -/
theorem span_range_domRestrict_eq_top [Finite ι] (hD : IsRootPlaneDecomposition B t α E J)
    (hrefl : B.IsRefl) (hani : B.toQuadraticMap.Anisotropic) (hinv : B.lieInvariant L) :
    Submodule.span K
        (Set.range fun i ↦ (α i).domRestrict ((derivedSeries K L 1).toSubmodule.comap t.subtype)) =
      ⊤ := by
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span K _),
    Submodule.dualAnnihilator_eq_top_iff, eq_bot_iff]
  intro H hH
  -- Every root vanishes at `H`, so `H` is central.
  have hα (i : ι) : α i H = 0 :=
    (Submodule.mem_dualCoannihilator H).mp hH _ (Submodule.subset_span ⟨i, rfl⟩)
  have hc : ((H : t) : L) ∈ center K L := hD.mem_center_of_forall_apply_eq_zero hα
  have hd : ((H : t) : L) ∈ derivedSeries K L 1 :=
    LieSubmodule.mem_toSubmodule _ |>.mp (Submodule.mem_comap.mp H.property)
  exact (Submodule.mem_bot K).mpr <| Subtype.ext <| Subtype.ext <|
    B.eq_zero_of_mem_center_of_mem_derivedSeries_one hrefl hani hinv hc hd

/-- **The coroot directions span the semisimple part of the torus.** For a reflexive invariant form
with anisotropic diagonal and a root-plane decomposition with nonzero roots, the
brackets `⁅v, J_i v⁆`, for `v` in a plane `E_i`, span `t ∩ [L, L]`. -/
theorem span_lie_eq_inf_derivedSeries [Finite ι] (hD : IsRootPlaneDecomposition B t α E J)
    (hα : ∀ i, α i ≠ 0) (hrefl : B.IsRefl)
    (hani : B.toQuadraticMap.Anisotropic) (hinv : B.lieInvariant L) :
    Submodule.span K {x | ∃ i, ∃ v : E i, ⁅(v : L), (J i v : L)⁆ = x} =
      t ⊓ (derivedSeries K L 1).toSubmodule := by
  set C := Submodule.span K {x | ∃ i, ∃ v : E i, ⁅(v : L), (J i v : L)⁆ = x}
  -- Every bracket `⁅v, J v⁆` commutes with `t` and lies in the derived algebra.
  have hCle : C ≤ t ⊓ (derivedSeries K L 1).toSubmodule := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, v, rfl⟩
    refine ⟨lie_mem_of_lie_eq_smul (fun z hz ↦ hD.mem_of_forall_lie_eq_zero hα hz)
      (fun H ↦ (hD.isRootPlane i).lie_apply H v) (fun H ↦ ?_), ?_⟩
    · rw [(hD.isRootPlane i).lie_apply, (hD.isRootPlane i).apply_apply, Submodule.coe_neg,
        smul_neg]
    · exact LieAlgebra.lie_mem_derivedSeries_one _ _
  -- A vector of `t` orthogonal to every bracket commutes with every plane, hence is central:
  -- for `v ≠ 0` in `E_i` it pairs with `⁅v, J_i v⁆` to `α_i(h) B(J_i v, J_i v)`, so `α_i(h) = 0`.
  have horth {h : L} (ht : h ∈ t) (hh : h ∈ B.orthogonal C) : h ∈ center K L := by
    refine hD.mem_center_of_forall_lie_eq_zero (H := ⟨h, ht⟩) fun i v ↦ ?_
    refine ((hD.isRootPlane i).lie_eq_zero_iff _ v).mpr ((eq_or_ne v 0).symm.imp (fun hv0 ↦ ?_) id)
    have hJv : (J i v : L) ≠ 0 := by
      rw [ne_eq, ZeroMemClass.coe_eq_zero, map_eq_zero_iff _ (hD.isRootPlane i).injective]
      exact hv0
    have hpair := LinearMap.BilinForm.lieInvariant.apply_lie_eq_mul_of_lie_eq_smul hinv
      (fun H ↦ (hD.isRootPlane i).lie_apply H v) ⟨h, ht⟩
    rw [hrefl _ _ (hh _ (Submodule.subset_span ⟨i, v, rfl⟩))] at hpair
    exact (mul_eq_zero.mp hpair.symm).resolve_right fun h0 ↦ hJv (hani _ h0)
  have hCcompl : IsCompl C (B.orthogonal C) := by
    refine B.isCompl_orthogonal_of_restrict_nondegenerate hrefl ?_
    rw [LinearMap.BilinForm.restrict_eq_compl₁₂]
    exact LinearMap.BilinForm.nondegenerate_of_anisotropic _
      (B.anisotropic_toQuadraticMap_compl₁₂ hani C.subtype C.injective_subtype)
  -- Write `x ∈ t ∩ [L, L]` as `c + h` with `c ∈ C` and `h ⊥ C`; then `h` is central and lies in
  -- the derived algebra, so it vanishes.
  refine le_antisymm hCle fun x ⟨hxt, hxd⟩ ↦ ?_
  obtain ⟨c, hc, h, hh, rfl⟩ :=
    Submodule.mem_sup.mp (hCcompl.sup_eq_top ▸ Submodule.mem_top (x := x))
  have hct := (hCle hc).1
  have hcd := (hCle hc).2
  have hht : h ∈ t := by simpa using t.sub_mem hxt hct
  have hhd : h ∈ (derivedSeries K L 1).toSubmodule := by
    simpa using (derivedSeries K L 1).toSubmodule.sub_mem hxd hcd
  have h0 : h = 0 := B.eq_zero_of_mem_center_of_mem_derivedSeries_one hrefl hani hinv
    (horth hht hh) hhd
  simpa [h0] using hc

end TauCeti.IsRootPlaneDecomposition
