/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Grassmannian
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Finite Grassmannians as quotients of frame spaces

For a field `𝕜` and natural numbers `r N`, `TauCeti.finiteGrassmannian 𝕜 r N` is the type of
`r`-dimensional subspaces of the coordinate space `Fin N → 𝕜`, as a subtype of
`Submodule 𝕜 (Fin N → 𝕜)`. A frame is a linearly independent `r`-tuple of vectors of
`Fin N → 𝕜`; frames form the subspace `TauCeti.finiteFullRankFrame 𝕜 r N` of
`Fin r → Fin N → 𝕜`. Taking spans gives `TauCeti.finiteGrassmannian.frameSpan`, and the
Grassmannian carries the quotient topology of this map.

Viewing a frame as the `r × N` matrix whose rows are its vectors, the general linear group
`GL (Fin r) 𝕜` acts on frames by left multiplication, which replaces the frame by another
basis of the same subspace. Two frames have the same span exactly when they lie in the same
orbit, so the Grassmannian is homeomorphic to the orbit space
(`TauCeti.finiteGrassmannian.orbitHomeomorph`). Over a topological ring of scalars, the action
is by homeomorphisms, and the span map is an open quotient map.

The degenerate ranks are handled explicitly: there is an `r`-dimensional subspace exactly when
`r ≤ N`, while the zero subspace and the whole space are the only points for `r = 0` and
`r = N`. Finally, `TauCeti.finiteGrassmannian.equivModuleGrassmannian` identifies the subspace
convention with Mathlib's `Module.Grassmannian 𝕜 (Fin N → 𝕜) (N - r)`, whose points are the
submodules with locally free quotient of rank `N - r`, without changing the underlying
submodule.

The construction of Grassmannians as quotients of frame spaces follows
J. Milnor and J. Stasheff, *Characteristic Classes*, §5.
-/

public section

open Set Topology

namespace TauCeti

variable (𝕜 : Type*) [Field 𝕜] (r N : ℕ)

/-- The finite Grassmannian of `r`-dimensional subspaces of the coordinate space `Fin N → 𝕜`. -/
abbrev finiteGrassmannian : Type _ :=
  {V : Submodule 𝕜 (Fin N → 𝕜) // Module.finrank 𝕜 V = r}

/-- The frames of `r` linearly independent vectors in the coordinate space `Fin N → 𝕜`, with the
topology inherited from `Fin r → Fin N → 𝕜`. -/
abbrev finiteFullRankFrame : Type _ :=
  {f : Fin r → Fin N → 𝕜 // LinearIndependent 𝕜 f}

namespace finiteFullRankFrame

variable {𝕜 r N}

/-- The general linear group acts on frames by left multiplication of the matrix of row
vectors: `A • f` has `j`th vector `∑ i, A j i • f i`. -/
instance : SMul (GL (Fin r) 𝕜) (finiteFullRankFrame 𝕜 r N) where
  smul A f := ⟨fun j => ∑ i, (A : Matrix (Fin r) (Fin r) 𝕜) j i • f.1 i, by
    -- The new vectors are the images of the rows of `A` under the injective map `c ↦ ∑ c i • f i`.
    have hinj : (Fintype.linearCombination 𝕜 f.1).ker = ⊥ :=
      LinearMap.ker_eq_bot.2 f.2.fintypeLinearCombination_injective
    convert (Matrix.linearIndependent_rows_of_isUnit (Units.isUnit A)).map' _ hinj using 1
    ext j : 1
    exact (Fintype.linearCombination_apply 𝕜 f.1 _).symm⟩

@[simp] theorem coe_smul (A : GL (Fin r) 𝕜) (f : finiteFullRankFrame 𝕜 r N) :
    ((A • f : finiteFullRankFrame 𝕜 r N) : Fin r → Fin N → 𝕜) =
      fun j => ∑ i, (A : Matrix (Fin r) (Fin r) 𝕜) j i • f.1 i := (rfl)

/-- Left multiplication of row vectors is an action of the general linear group on frames. -/
instance : MulAction (GL (Fin r) 𝕜) (finiteFullRankFrame 𝕜 r N) where
  one_smul f := by
    ext j : 2
    simp [Matrix.one_apply]
  mul_smul A B f := by
    ext j : 2
    simp only [coe_smul, Units.val_mul, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum,
      smul_smul]
    exact Finset.sum_comm

/-- Over a topological ring, each element of the general linear group acts continuously on
frames. -/
instance [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] :
    ContinuousConstSMul (GL (Fin r) 𝕜) (finiteFullRankFrame 𝕜 r N) where
  continuous_const_smul A := by
    refine Continuous.subtype_mk (continuous_pi fun j => continuous_finsetSum _ fun i _ => ?_) _
    exact ((continuous_apply i : Continuous fun p : Fin r → Fin N → 𝕜 => p i).comp
      continuous_subtype_val).const_smul ((A : Matrix (Fin r) (Fin r) 𝕜) j i)

end finiteFullRankFrame

namespace finiteGrassmannian

variable {𝕜 r N}

/-- The span of a frame, an `r`-dimensional subspace of `Fin N → 𝕜`. -/
noncomputable def frameSpan (f : finiteFullRankFrame 𝕜 r N) : finiteGrassmannian 𝕜 r N :=
  ⟨Submodule.span 𝕜 (range f.1), by rw [finrank_span_eq_card f.2, Fintype.card_fin]⟩

@[simp] theorem coe_frameSpan (f : finiteFullRankFrame 𝕜 r N) :
    (frameSpan f : Submodule 𝕜 (Fin N → 𝕜)) = Submodule.span 𝕜 (range f.1) := (rfl)

/-- Every `r`-dimensional subspace is spanned by a frame. -/
theorem frameSpan_surjective :
    Function.Surjective (frameSpan : finiteFullRankFrame 𝕜 r N → _) := by
  rintro ⟨V, hV⟩
  let b := Module.finBasisOfFinrankEq 𝕜 V hV
  refine ⟨⟨V.subtype ∘ b, b.linearIndependent.map' V.subtype V.ker_subtype⟩, Subtype.ext ?_⟩
  rw [coe_frameSpan, range_comp, Submodule.span_image, b.span_eq, Submodule.map_top,
    Submodule.range_subtype]

/-- The vectors of `A • f` lie in the span of `f`. -/
private theorem span_range_smul_le (A : GL (Fin r) 𝕜) (f : finiteFullRankFrame 𝕜 r N) :
    Submodule.span 𝕜 (range (A • f).1) ≤ Submodule.span 𝕜 (range f.1) :=
  Submodule.span_le.2 <| range_subset_iff.2 fun j => by
    rw [finiteFullRankFrame.coe_smul]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

@[simp] theorem frameSpan_smul (A : GL (Fin r) 𝕜) (f : finiteFullRankFrame 𝕜 r N) :
    frameSpan (A • f) = frameSpan f := by
  refine Subtype.ext ?_
  rw [coe_frameSpan, coe_frameSpan]
  refine le_antisymm (span_range_smul_le A f) ?_
  simpa only [inv_smul_smul] using span_range_smul_le A⁻¹ (A • f)

/-- Two frames span the same subspace exactly when they lie in the same orbit of the general
linear group. -/
theorem frameSpan_eq_frameSpan_iff {f g : finiteFullRankFrame 𝕜 r N} :
    frameSpan f = frameSpan g ↔ g ∈ MulAction.orbit (GL (Fin r) 𝕜) f := by
  refine ⟨fun h => ?_, ?_⟩
  · -- Write each vector of `g` in terms of `f`; the coefficient matrix has independent rows.
    have hg : ∀ j, ∃ c : Fin r → 𝕜, ∑ i, c i • f.1 i = g.1 j := fun j =>
      Submodule.mem_span_range_iff_exists_fun 𝕜 |>.1 <| by
        rw [← coe_frameSpan, h, coe_frameSpan]
        exact Submodule.subset_span (mem_range_self j)
    choose c hc using hg
    have hcomp : Fintype.linearCombination 𝕜 f.1 ∘ c = g.1 := by
      ext1 j
      simp [Fintype.linearCombination_apply, hc]
    have hrow : LinearIndependent 𝕜 c :=
      LinearIndependent.of_comp (Fintype.linearCombination 𝕜 f.1) (by rw [hcomp]; exact g.2)
    exact ⟨(Matrix.linearIndependent_row_iff_isUnit.1 hrow).unit, Subtype.ext <| funext hc⟩
  · rintro ⟨A, rfl⟩
    exact (frameSpan_smul A f).symm

/-- The frame-span map descends to a bijection from the orbit space of frames under the general
linear group onto the finite Grassmannian. -/
theorem bijective_lift_frameSpan :
    Function.Bijective (Quotient.lift (s := MulAction.orbitRel (GL (Fin r) 𝕜) _)
      (frameSpan : finiteFullRankFrame 𝕜 r N → _) fun _ _ h =>
        (frameSpan_eq_frameSpan_iff.2 (MulAction.orbitRel_apply.1 h)).symm) :=
  ⟨fun x y => Quotient.inductionOn₂ x y fun _ _ h =>
      Quotient.sound (MulAction.orbitRel_apply.2 (frameSpan_eq_frameSpan_iff.1 h.symm)),
    fun V => let ⟨f, hf⟩ := frameSpan_surjective V; ⟨Quotient.mk _ f, hf⟩⟩

/-- There is an `r`-dimensional subspace of `Fin N → 𝕜` exactly when `r ≤ N`. -/
theorem nonempty_iff_le : Nonempty (finiteGrassmannian 𝕜 r N) ↔ r ≤ N := by
  refine ⟨fun ⟨V⟩ => ?_, fun h => ⟨frameSpan ⟨fun i => Pi.single (Fin.castLE h i) 1, ?_⟩⟩⟩
  · simpa [V.2] using Submodule.finrank_le V.1
  · simpa [Function.comp_def] using
      (Pi.basisFun 𝕜 (Fin N)).linearIndependent.comp _ (Fin.castLE_injective h)

/-- There is no `r`-dimensional subspace of `Fin N → 𝕜` exactly when `N < r`. -/
theorem isEmpty_iff_lt : IsEmpty (finiteGrassmannian 𝕜 r N) ↔ N < r := by
  rw [← not_nonempty_iff, nonempty_iff_le, not_le]

/-- For `N < r`, there is no `r`-dimensional subspace of `Fin N → 𝕜`. -/
theorem isEmpty_of_lt (h : N < r) : IsEmpty (finiteGrassmannian 𝕜 r N) :=
  isEmpty_iff_lt.2 h

/-- The zero subspace is the unique point of the rank-zero Grassmannian. -/
instance : Unique (finiteGrassmannian 𝕜 0 N) where
  default := ⟨⊥, finrank_bot 𝕜 _⟩
  uniq V := Subtype.ext (Submodule.finrank_eq_zero.1 V.2)

@[simp] theorem coe_default_zero :
    ((default : finiteGrassmannian 𝕜 0 N) : Submodule 𝕜 (Fin N → 𝕜)) = ⊥ := (rfl)

/-- The only `N`-dimensional subspace of `Fin N → 𝕜` is the whole space. -/
@[simp] theorem coe_eq_top (V : finiteGrassmannian 𝕜 N N) :
    (V : Submodule 𝕜 (Fin N → 𝕜)) = ⊤ :=
  Submodule.eq_top_of_finrank_eq (V.2.trans (Module.finrank_fin_fun 𝕜).symm)

/-- The full-rank Grassmannian has at most one point; it is nonempty by `nonempty_iff_le`. -/
instance : Subsingleton (finiteGrassmannian 𝕜 N N) :=
  ⟨fun V W => Subtype.ext ((coe_eq_top V).trans (coe_eq_top W).symm)⟩

/-- The quotient by an `r`-dimensional subspace of `Fin N → 𝕜` has dimension `N - r`. -/
theorem finrank_quotient (V : finiteGrassmannian 𝕜 r N) :
    Module.finrank 𝕜 ((Fin N → 𝕜) ⧸ V.1) = N - r := by
  rw [Submodule.finrank_quotient, Module.finrank_fin_fun, V.2]

/-- The rank at every stalk of a quotient of `Fin N → 𝕜` is the dimension of the quotient. -/
private theorem rankAtStalk_quotient (W : Submodule 𝕜 (Fin N → 𝕜)) (p : PrimeSpectrum 𝕜) :
    Module.rankAtStalk ((Fin N → 𝕜) ⧸ W) p = N - Module.finrank 𝕜 W := by
  rw [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id,
    Submodule.finrank_quotient, Module.finrank_fin_fun]

variable (𝕜) in
/-- For `r ≤ N`, the `r`-dimensional subspaces of `Fin N → 𝕜` are the points of Mathlib's
Grassmannian `Module.Grassmannian 𝕜 (Fin N → 𝕜) (N - r)`, whose points are the submodules with
quotient of rank `N - r`. The underlying submodule is unchanged. -/
noncomputable def equivModuleGrassmannian (h : r ≤ N) :
    finiteGrassmannian 𝕜 r N ≃ Module.Grassmannian 𝕜 (Fin N → 𝕜) (N - r) where
  toFun V :=
    { toSubmodule := V.1
      finite_quotient := inferInstance
      projective_quotient := inferInstance
      rankAtStalk_eq := fun p => by rw [rankAtStalk_quotient, V.2] }
  invFun W := ⟨W.toSubmodule, by
    have hW := W.rankAtStalk_eq (Nonempty.some inferInstance)
    rw [rankAtStalk_quotient] at hW
    have hle := (Submodule.finrank_le W.toSubmodule).trans_eq (Module.finrank_fin_fun 𝕜)
    omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem toSubmodule_equivModuleGrassmannian_apply (h : r ≤ N)
    (V : finiteGrassmannian 𝕜 r N) :
    (equivModuleGrassmannian 𝕜 h V).toSubmodule = V.1 := (rfl)

@[simp] theorem coe_equivModuleGrassmannian_symm_apply (h : r ≤ N)
    (W : Module.Grassmannian 𝕜 (Fin N → 𝕜) (N - r)) :
    ((equivModuleGrassmannian 𝕜 h).symm W : Submodule 𝕜 (Fin N → 𝕜)) = W.toSubmodule := (rfl)

/-- The finite Grassmannian carries the quotient topology of the frame-span map. -/
noncomputable instance [TopologicalSpace 𝕜] : TopologicalSpace (finiteGrassmannian 𝕜 r N) :=
  .coinduced frameSpan inferInstance

variable [TopologicalSpace 𝕜]

/-- The frame-span map is a quotient map, by definition of the topology of the Grassmannian. -/
theorem isQuotientMap_frameSpan :
    IsQuotientMap (frameSpan : finiteFullRankFrame 𝕜 r N → _) :=
  ⟨⟨rfl⟩, frameSpan_surjective⟩

@[fun_prop]
theorem continuous_frameSpan : Continuous (frameSpan : finiteFullRankFrame 𝕜 r N → _) :=
  isQuotientMap_frameSpan.continuous

variable (𝕜 r N) in
/-- The finite Grassmannian is homeomorphic to the space of orbits of frames under the general
linear group, by taking the span of a representative frame. -/
noncomputable def orbitHomeomorph :
    MulAction.orbitRel.Quotient (GL (Fin r) 𝕜) (finiteFullRankFrame 𝕜 r N) ≃ₜ
      finiteGrassmannian 𝕜 r N where
  toEquiv := Equiv.ofBijective _ bijective_lift_frameSpan
  continuous_toFun := continuous_quot_lift _ continuous_frameSpan
  continuous_invFun := by
    rw [isQuotientMap_frameSpan.continuous_iff]
    exact continuous_quot_mk.congr fun f =>
      ((Equiv.ofBijective _ bijective_lift_frameSpan).symm_apply_apply (Quotient.mk _ f)).symm

@[simp] theorem orbitHomeomorph_mk (f : finiteFullRankFrame 𝕜 r N) :
    orbitHomeomorph 𝕜 r N (Quotient.mk _ f) = frameSpan f := (rfl)

@[simp] theorem orbitHomeomorph_symm_frameSpan (f : finiteFullRankFrame 𝕜 r N) :
    (orbitHomeomorph 𝕜 r N).symm (frameSpan f) = Quotient.mk _ f :=
  (orbitHomeomorph 𝕜 r N).symm_apply_eq.2 (orbitHomeomorph_mk f).symm

/-- Over a topological ring, the frame-span map is an open quotient map. -/
theorem isOpenQuotientMap_frameSpan [IsTopologicalRing 𝕜] :
    IsOpenQuotientMap (frameSpan : finiteFullRankFrame 𝕜 r N → _) := by
  convert (orbitHomeomorph 𝕜 r N).isOpenQuotientMap.comp
    MulAction.isOpenQuotientMap_quotientMk using 1
  exact funext fun f => (orbitHomeomorph_mk f).symm

end finiteGrassmannian

end TauCeti
