/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.Algebra.Lie.Cohomology.Continuous
public import TauCeti.Algebra.Lie.Extension.Basic

/-!
# The topology of an extension by a discrete module

Let `L` be a Lie algebra with a topology and `c` a 2-cocycle of `L` with values in an `L`-module
`M`. This file gives Mathlib's sheared Lie algebra `LieAlgebra.ofTwoCocycle c` the topology of
`L × M` in which `M` is **discrete**, transported along `LieAlgebra.ofProd`. This is the
convention of continuous cohomology with discrete coefficients
(`TauCeti.LieModule.Cohomology.continuousTwoCochain`): no topology on `M` is used, so an existing
topology on `M` (for instance on `ℂ`) is ignored rather than changed.

In this topology:

* the identification `ofProd` with `L × M` is a homeomorphism as soon as `M` carries some discrete
  topology (`LieAlgebra.ofTwoCocycle.ofProdContinuousLinearEquiv`), and a map into the extension
  is continuous exactly when its `L`-coordinate is continuous and its `M`-coordinate is locally
  constant (`LieAlgebra.ofTwoCocycle.continuous_iff`);
* the projection onto `L` is a continuous open quotient map, the linear section
  `x ↦ (x, 0)` (`LieAlgebra.ofTwoCocycle.inl`) is a continuous open embedding, and its image is an
  open subspace meeting the kernel `0 × M` only in zero. The kernel of the projection is discrete
  in its subspace topology, and closed when the points of `L` are closed;
* the extension is a topological additive group when `L` is, and it is Hausdorff when `L` is;
* the bracket of the extension is continuous exactly when the bracket of `L` is continuous, the
  cocycle `c` is continuous, and every element of `M` is annihilated by a neighbourhood of zero
  (`LieAlgebra.ofTwoCocycle.continuous_lie_iff`).

The isomorphism `LieAlgebra.LieEquiv.ofCoboundary` between the extensions of two cohomologous
cocycles `c' = c + d₁₂ f` is a homeomorphism exactly when the one-cochain `f` is continuous, and
the morphisms of central extensions `LieAlgebra.ofTwoCocycle.map` are continuous whenever the map
of quotients is. Thus cocycles with the same class in continuous second cohomology give
isomorphic topological Lie algebras.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3, for central extensions of the
  formal loop algebra as topological Lie algebras with a discrete central kernel.
-/

public section

open Filter Topology LieModule.Cohomology TauCeti.LieModule.Cohomology

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M] [TopologicalSpace L]

namespace LieAlgebra.ofTwoCocycle

variable (c : twoCocycle R L M)

/-- The topology on the Lie algebra sheared by a 2-cocycle: the product of the topology of `L`
and the discrete topology of the coefficients `M`, transported along `ofProd`. Any topology on
`M` itself is ignored. -/
instance instTopologicalSpace : TopologicalSpace (ofTwoCocycle c) :=
  .induced (ofProd c).symm (@instTopologicalSpaceProd L M _ ⊥)

/-- For any discrete topology on the coefficients, the identification `ofProd` of `L × M` with the
sheared Lie algebra is a continuous linear equivalence. -/
def ofProdContinuousLinearEquiv [TopologicalSpace M] [DiscreteTopology M] :
    (L × M) ≃L[R] ofTwoCocycle c where
  toFun := ofProd c
  invFun := (ofProd c).symm
  map_add' := of_add c
  map_smul' := of_smul c
  left_inv := (ofProd c).left_inv
  right_inv := (ofProd c).right_inv
  continuous_toFun := by
    obtain rfl := DiscreteTopology.eq_bot (α := M)
    refine continuous_induced_rng.2 ?_
    rw [Equiv.symm_comp_self]
    exact @continuous_id _ (@instTopologicalSpaceProd L M _ ⊥)
  continuous_invFun := by
    obtain rfl := DiscreteTopology.eq_bot (α := M)
    exact continuous_induced_dom

@[simp]
lemma coe_ofProdContinuousLinearEquiv [TopologicalSpace M] [DiscreteTopology M] :
    ⇑(ofProdContinuousLinearEquiv c) = ofProd c := (rfl)

@[simp]
lemma coe_ofProdContinuousLinearEquiv_symm [TopologicalSpace M] [DiscreteTopology M] :
    ⇑(ofProdContinuousLinearEquiv c).symm = (ofProd c).symm := (rfl)

variable {c}

/-- **Continuity of maps into an extension.** A map into the sheared Lie algebra is continuous
exactly when its `L`-coordinate is continuous and its coefficient coordinate is locally
constant. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → ofTwoCocycle c} :
    Continuous f ↔ Continuous (fun x ↦ ((ofProd c).symm (f x)).1) ∧
      IsLocallyConstant fun x ↦ ((ofProd c).symm (f x)).2 := by
  let : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  rw [IsLocallyConstant.iff_continuous, ← continuous_prodMk,
    ← (ofProdContinuousLinearEquiv c).symm.toHomeomorph.comp_continuous_iff]
  exact Iff.rfl

variable (c)

/-- The `L`-coordinate is continuous. -/
theorem continuous_ofProd_symm_fst : Continuous fun v : ofTwoCocycle c ↦ ((ofProd c).symm v).1 :=
  (continuous_iff.mp continuous_id').1

/-- The projection onto `L` is continuous. -/
theorem continuous_proj : Continuous (proj c) := by
  simpa only [funext (proj_apply c)] using continuous_ofProd_symm_fst c

/-- The coefficient coordinate is locally constant. -/
theorem isLocallyConstant_snd : IsLocallyConstant fun v : ofTwoCocycle c ↦ ((ofProd c).symm v).2 :=
  (continuous_iff.mp continuous_id').2

/-- The projection onto `L` is an open quotient map. -/
theorem isOpenQuotientMap_proj : IsOpenQuotientMap (proj c) := by
  let : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  rw [funext (proj_apply c)]
  exact isOpenQuotientMap_fst.comp
    (ofProdContinuousLinearEquiv c).symm.toHomeomorph.isOpenQuotientMap

/-- The linear section `x ↦ (x, 0)` of the projection, as a continuous linear map. -/
def inl : L →L[R] ofTwoCocycle c where
  toFun x := ofProd c (x, 0)
  map_add' x y := by simp [← of_add]
  map_smul' r x := by simp [← of_smul]
  cont := by
    refine continuous_iff.mpr ⟨by simpa using continuous_id', ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact IsLocallyConstant.const _

@[simp]
lemma inl_apply (x : L) : inl c x = ofProd c (x, 0) := (rfl)

/-- The section `inl` is a right inverse of the projection. -/
lemma proj_inl (x : L) : proj c (inl c x) = x := by
  simp

/-- The image of the section `inl` is the open subspace `L × 0`. -/
theorem isOpen_range_inl : IsOpen (Set.range (inl c)) := by
  have h : Set.range (inl c) = (fun v ↦ ((ofProd c).symm v).2) ⁻¹' {0} := by
    ext v
    refine ⟨?_, fun hv ↦ ⟨((ofProd c).symm v).1, (ofProd c).symm.injective ?_⟩⟩
    · rintro ⟨x, rfl⟩
      simp
    · exact Prod.ext (by simp) (by simpa using hv.symm)
  rw [h]
  exact (isLocallyConstant_snd c).isOpen_fiber 0

/-- **The section is an open embedding.** The linear section `x ↦ (x, 0)` of the projection is a
homeomorphism onto the open subspace `L × 0`. -/
theorem isOpenEmbedding_inl : IsOpenEmbedding (inl c) :=
  .of_continuous_injective_isOpenMap (inl c).continuous
    (Function.LeftInverse.injective (proj_inl c)) fun U hU ↦ by
      have : inl c '' U = Set.range (inl c) ∩ proj c ⁻¹' U := by
        ext v
        refine ⟨?_, fun ⟨⟨x, hx⟩, hv⟩ ↦ ⟨x, by simpa [← hx] using hv, hx⟩⟩
        rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, rfl⟩, by simpa using hx⟩
      rw [this]
      exact (isOpen_range_inl c).inter (hU.preimage (continuous_proj c))

/-- The image of the section meets the kernel of the projection only in zero. -/
theorem range_inl_inter_ker_proj :
    Set.range (inl c) ∩ (proj c).ker = {0} := by
  ext v
  simp only [Set.mem_inter_iff, Set.mem_range, SetLike.mem_coe, mem_ker_proj,
    Set.mem_singleton_iff]
  refine ⟨fun ⟨⟨x, hx⟩, hv⟩ ↦ ?_, ?_⟩
  · subst hx
    simp_all [← of_zero]
  · rintro rfl
    exact ⟨⟨0, by simp [← of_zero]⟩, by simp⟩

/-- The kernel `0 × M` of the projection is discrete in its subspace topology. -/
instance : DiscreteTopology (proj c).ker := by
  refine discreteTopology_iff_isOpen_singleton.mpr fun v ↦ ?_
  have h : ({v} : Set (proj c).ker) =
      Subtype.val ⁻¹' ((fun w ↦ ((ofProd c).symm w).2) ⁻¹' {((ofProd c).symm v.1).2}) := by
    ext w
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    refine ⟨fun h ↦ h ▸ rfl, fun h ↦ Subtype.ext ((ofProd c).symm.injective ?_)⟩
    exact Prod.ext (((mem_ker_proj c).mp w.2).trans ((mem_ker_proj c).mp v.2).symm) h
  rw [h]
  exact ((isLocallyConstant_snd c).isOpen_fiber _).preimage continuous_subtype_val

/-- The kernel `0 × M` of the projection is closed when the points of `L` are closed. -/
theorem isClosed_ker_proj [T1Space L] : IsClosed ((proj c).ker : Set (ofTwoCocycle c)) :=
  isClosed_singleton.preimage (continuous_proj c)

instance [T2Space L] : T2Space (ofTwoCocycle c) := by
  let : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  exact (ofProdContinuousLinearEquiv c).toHomeomorph.t2Space

instance [IsTopologicalAddGroup L] : IsTopologicalAddGroup (ofTwoCocycle c) := by
  let : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  exact (ofProdContinuousLinearEquiv c).symm.toHomeomorph.isInducing.isTopologicalAddGroup
    (ofProdContinuousLinearEquiv c).symm.toLinearMap

/-! ### Continuity of morphisms of extensions -/

section Trivial

variable {L' M' : Type*} [LieRing L'] [LieAlgebra R L'] [TopologicalSpace L'] [AddCommGroup M']
  [Module R M'] [LieRingModule L' M'] [LieModule R L' M'] [LieModule.IsTrivial L M]
  [LieModule.IsTrivial L' M']

/-- A morphism of central extensions is continuous when its map of quotients is; no condition is
needed on the map of the discrete coefficients. -/
theorem continuous_map {φ : L →ₗ⁅R⁆ L'} (hφ : Continuous φ) (e : M →ₗ[R] M')
    (c' : twoCocycle R L' M')
    (h : ∀ x y, (c' : twoCochain R L' M') (φ x) (φ y) = e ((c : twoCochain R L M) x y)) :
    Continuous (map c φ e c' h) := by
  refine continuous_iff.mpr ⟨?_, ?_⟩
  · simpa [Function.comp_def] using hφ.comp (continuous_proj c)
  · simpa [Function.comp_def] using (isLocallyConstant_snd c).comp e

end Trivial

/-! ### Continuity of the bracket -/

variable [IsTopologicalAddGroup L]

/-- **Continuity of the bracket of an extension.** The bracket of the sheared Lie algebra is
continuous exactly when the bracket of `L` is continuous, the cocycle `c` is continuous, and every
element of `M` is annihilated by a neighbourhood of zero in `L`. -/
theorem continuous_lie_iff :
    (Continuous fun p : ofTwoCocycle c × ofTwoCocycle c ↦ ⁅p.1, p.2⁆) ↔
      (Continuous fun p : L × L ↦ ⁅p.1, p.2⁆) ∧
        (c : twoCochain R L M) ∈ continuousTwoCochain R L M ∧
        ∀ m : M, ∀ᶠ x in 𝓝 (0 : L), ⁅x, m⁆ = 0 := by
  let : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  have hc := mem_continuousTwoCochain_iff_continuous (R := R) (L := L) (M := M)
    (c := (c : twoCochain R L M))
  refine ⟨fun h ↦ ⟨?_, ?_, fun m ↦ ?_⟩, fun ⟨hL, hcont, hM⟩ ↦ ?_⟩
  · -- Brackets of elements of the section have first coordinate the bracket in `L`.
    simpa [bracket_ofTwoCocycle, Function.comp_def] using (continuous_proj c).comp
      (h.comp ((inl c).continuous.prodMap (inl c).continuous))
  · -- Brackets of elements of the section have second coordinate the value of `c`.
    refine hc.mpr ?_
    have := (isLocallyConstant_snd c).continuous.comp
      (h.comp ((inl c).continuous.prodMap (inl c).continuous))
    simpa [bracket_ofTwoCocycle, Function.comp_def] using this
  · -- The bracket of `(x, 0)` with `(0, m)` is `(0, ⁅x, m⁆)`, locally constant in `x`.
    have := (isLocallyConstant_snd c).continuous.comp
      (h.comp ((inl c).continuous.prodMk (continuous_const (y := ofProd c (0, m)))))
    simpa [bracket_ofTwoCocycle, Function.comp_def, nhds_discrete M] using this.tendsto 0
  · refine continuous_iff.mpr ⟨?_, ?_⟩
    · simpa [bracket_ofTwoCocycle, Function.comp_def] using
        hL.comp ((continuous_proj c).prodMap (continuous_proj c))
    · -- The coefficient coordinate `c x y + ⁅x, n⁆ - ⁅y, m⁆` is a sum of continuous maps into
      -- the discrete module `M`.
      have hact : Continuous fun p : L × M ↦ ⁅p.1, p.2⁆ :=
        continuous_prod_of_discrete_right.mpr fun n ↦ by
          refine ((mem_continuousOneCochain_iff_continuous
            (f := (LieModule.toEnd R L M : L →ₗ[R] Module.End R M).flip n)).mp
              (mem_continuousOneCochain_iff.mpr (by simpa using hM n))).congr fun x ↦ ?_
          simp
      have hp := continuous_proj c
      have hs := (isLocallyConstant_snd c).continuous
      have h₁ := (hc.mp hcont).comp (hp.prodMap hp)
      have h₂ := hact.comp ((hp.comp continuous_fst).prodMk (hs.comp continuous_snd))
      have h₃ := hact.comp ((hp.comp continuous_snd).prodMk (hs.comp continuous_fst))
      rw [IsLocallyConstant.iff_continuous]
      refine ((h₁.add h₂).sub h₃).congr fun p ↦ ?_
      simp [bracket_ofTwoCocycle]

/-! ### Cohomologous cocycles -/

/-- **Cohomologous cocycles give homeomorphic extensions.** The isomorphism
`LieEquiv.ofCoboundary` from the extension of `c` to that of `c' = c + d₁₂ f`, which is
`(x, m) ↦ (x, m - f x)`, is continuous exactly when `f` is a continuous one-cochain. -/
theorem continuous_ofCoboundary_iff (c' : twoCocycle R L M) (f : oneCochain R L M)
    (h : c' = c + d₁₂ R L M f) :
    Continuous (LieEquiv.ofCoboundary c c' f h) ↔ f ∈ continuousOneCochain R L M := by
  let : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  have hp := continuous_ofProd_symm_fst c
  have hv (v : ofTwoCocycle c) : (ofProd c').symm (LieEquiv.ofCoboundary c c' f h v) =
      (((ofProd c).symm v).1, ((ofProd c).symm v).2 - f ((ofProd c).symm v).1) := by
    simp
  simp only [mem_continuousOneCochain_iff_continuous, continuous_iff, hv,
    IsLocallyConstant.iff_continuous]
  refine ⟨fun ⟨_, hf⟩ ↦ ?_, fun hf ↦ ⟨hp, (isLocallyConstant_snd c).continuous.sub (hf.comp hp)⟩⟩
  -- On the section `x ↦ (x, 0)` the coefficient coordinate is `-f x`.
  simpa [Function.comp_def] using (hf.comp (inl c).continuous).neg

/-- The inverse `(x, m) ↦ (x, m + f x)` of the isomorphism `LieEquiv.ofCoboundary` is continuous
when `f` is a continuous one-cochain. -/
theorem continuous_ofCoboundary_symm (c' : twoCocycle R L M) {f : oneCochain R L M}
    (h : c' = c + d₁₂ R L M f) (hf : f ∈ continuousOneCochain R L M) :
    Continuous (LieEquiv.ofCoboundary c c' f h).symm := by
  let : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  have hp := continuous_ofProd_symm_fst c'
  have hv (v : ofTwoCocycle c') : (ofProd c).symm ((LieEquiv.ofCoboundary c c' f h).symm v) =
      (((ofProd c').symm v).1, ((ofProd c').symm v).2 + f ((ofProd c').symm v).1) := by
    rw [Equiv.symm_apply_eq, LieEquiv.symm_apply_eq]
    simp
  rw [mem_continuousOneCochain_iff_continuous] at hf
  simp only [continuous_iff, hv, IsLocallyConstant.iff_continuous]
  exact ⟨hp, (isLocallyConstant_snd c').continuous.add (hf.comp hp)⟩

end LieAlgebra.ofTwoCocycle
