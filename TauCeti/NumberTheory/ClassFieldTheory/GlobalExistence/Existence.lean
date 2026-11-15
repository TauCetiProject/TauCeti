/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.NormSubgroup

import TauCeti.NumberTheory.ClassFieldTheory.Formation.ExistenceInduction
import TauCeti.NumberTheory.ClassFieldTheory.Global.ClassFormation
import TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.Kummer

/-!
# Global existence

Let `K` be a number field. This file proves the **global existence theorem**: every open subgroup
of finite index of the idele class group `C_K` is the norm subgroup of a finite abelian extension
of `K` (`globalAbelianExistence`), and in particular of some finite Galois extension
(`globalExistence`).

The proof is the induction on the index of Milne, *Class Field Theory*, VII, Theorem 9.5, run in
the idele-class formation `globalFormation K` through
`ClassFormation.exists_abelianLayer_normSubgroup_eq_of_forall_prime`. Its level at an open
subgroup `W` of `G_K` is the idele class group `C_F` of the fixed field `F` of `W`
(`ideleClassLevelEquiv`), and the norms between levels are the idele-class norms
(`levelNorm_ideleClassLevelEquiv`). The admissible subgroups of a level are those that are open in
`C_F`; they are closed under enlargement and, the idele-class norms being continuous, under
preimages by norms. It remains to supply the Kummer case at every level: given a prime `p` and an
open subgroup `W` with fixed field `F`, pass to the open subgroup `W'` fixing `E = F(ζ_p)`, where
`ζ_p` is a primitive `p`-th root of unity in `Kˢ`. An open subgroup of `C_E` containing the
`p`-th powers is the norm subgroup of an abelian extension `M/E`
(`exists_abelianLayer_globalNormSubgroup_eq_of_pow_mem`, Milne VII, Lemma 9.3). Embedding `M` into
`Kˢ` over `E` (`exists_intermediateField_range_ideleClassNormMap_eq_of_pow_mem`), its norm group is
the image of the norm from the level of the open subgroup fixing the image of `M`.

## Main results

* `TauCeti.ClassFieldTheory.globalAbelianExistence`: every open subgroup of finite index of `C_K`
  is the norm subgroup of an abelian layer of `G_K`.
* `TauCeti.ClassFieldTheory.globalExistence`: its forgetful form.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §9, Lemma 9.3 and Theorem 9.5.
* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §6.
-/

public noncomputable section

open IntermediateField NumberField

namespace TauCeti.ClassFieldTheory

open GlobalNumberFields

variable {K : Type} [Field K] [NumberField K]

/-! ### Open subgroups of the levels -/

/-- The subgroup of the idele class group `C_F` of the fixed field `F` of an open subgroup `W` of
`G_K` that corresponds to a subgroup `N` of the level of `W` under `ideleClassLevelEquiv`. -/
private def levelSubgroup {W : OpenSubgroup (AbsoluteGaloisGroup K)}
    {F : IntermediateField K (SeparableClosure K)} [NumberField F]
    (hF : fixedField W.toSubgroup = F) (N : AddSubgroup ((globalFormation K).level W)) :
    Subgroup (IdeleClassGroup (𝓞 F) F) :=
  AddSubgroup.toSubgroup' (N.comap (ideleClassLevelEquiv hF).toAddMonoidHom)

private theorem mem_levelSubgroup {W : OpenSubgroup (AbsoluteGaloisGroup K)}
    {F : IntermediateField K (SeparableClosure K)} [NumberField F]
    {hF : fixedField W.toSubgroup = F} {N : AddSubgroup ((globalFormation K).level W)}
    {c : IdeleClassGroup (𝓞 F) F} :
    c ∈ levelSubgroup hF N ↔ ideleClassLevelEquiv hF (.ofMul c) ∈ N :=
  Iff.rfl

/-- A subgroup of the level of `W` is *open* when the corresponding subgroup of the idele class
group of the fixed field of `W` is open. These are the admissible subgroups of the induction on
the index. -/
private def IsOpenLevel (W : OpenSubgroup (AbsoluteGaloisGroup K))
    (N : AddSubgroup ((globalFormation K).level W)) : Prop :=
  ∀ (F : IntermediateField K (SeparableClosure K)) [NumberField F]
    (hF : fixedField W.toSubgroup = F),
    IsOpen (levelSubgroup hF N : Set (IdeleClassGroup (𝓞 F) F))

/-- Open subgroups of a level are closed under enlargement. -/
private theorem IsOpenLevel.mono {W : OpenSubgroup (AbsoluteGaloisGroup K)}
    {N N' : AddSubgroup ((globalFormation K).level W)} (hN : IsOpenLevel W N) (h : N ≤ N') :
    IsOpenLevel W N' :=
  fun F _ hF ↦ Subgroup.isOpen_mono (fun _ hc ↦ h hc) (hN F hF)

/-- Open subgroups of a level are closed under preimages by the norms between levels, which are the
continuous idele-class norms. -/
private theorem IsOpenLevel.comap {W W' : OpenSubgroup (AbsoluteGaloisGroup K)} (h : W' ≤ W)
    {N : AddSubgroup ((globalFormation K).level W)} (hN : IsOpenLevel W N) :
    IsOpenLevel W' (N.comap ((globalFormation K).levelNorm h)) := by
  intro L _ hL
  have : NumberField (fixedField W.toSubgroup) := .of_module_finite K _
  have hFL : fixedField W.toSubgroup ≤ L :=
    hL ▸ fixedField_antitone (OpenSubgroup.toSubgroup_le.2 h)
  let _ := (inclusion hFL).toRingHom.toAlgebra
  have : IsScalarTower (fixedField W.toSubgroup) L (SeparableClosure K) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have heq : (levelSubgroup hL (N.comap ((globalFormation K).levelNorm h)) :
      Set (IdeleClassGroup (𝓞 L) L)) =
        ideleClassNormMap (fixedField W.toSubgroup) L ⁻¹' levelSubgroup rfl N := by
    ext c
    exact (congrArg (· ∈ N) (levelNorm_ideleClassLevelEquiv h rfl hL c)).to_iff
  rw [heq]
  exact (hN _ rfl).preimage (continuous_ideleClassNormMap _ _)

/-- The subgroup of the ground level corresponding to an open subgroup of `C_K` is open. -/
private theorem isOpenLevel_globalGroundOrderIso {N : Subgroup (IdeleClassGroup (𝓞 K) K)}
    (hN : IsOpen (N : Set (IdeleClassGroup (𝓞 K) K))) :
    IsOpenLevel ⊤ (globalGroundOrderIso K N).toAddSubgroup := by
  intro F _ hF
  -- The fixed field of `G_K` is the bottom subextension, finite and Galois over `K`.
  obtain ⟨E, rfl⟩ : ∃ E : FiniteGaloisIntermediateField K (SeparableClosure K),
      (E : IntermediateField K (SeparableClosure K)) = F :=
    ⟨⊥, (TauCeti.fixedField_toSubgroup_top K).symm.trans hF⟩
  -- Read in `C_K`, the level element of `c ∈ C_F` is the norm of `c` from `F` to `K`.
  have key (c : IdeleClassGroup (𝓞 E) E) :
      ideleClassLevelEquiv hF (.ofMul c) =
        globalGroundEquiv K (.ofMul (ideleClassNormMap K E c)) := by
    rw [← levelNorm_top_ideleClassLevelEquiv E le_rfl hF, Formation.levelNorm_self,
      AddMonoidHom.id_apply]
  have heq : (levelSubgroup hF (globalGroundOrderIso K N).toAddSubgroup :
      Set (IdeleClassGroup (𝓞 E) E)) = ideleClassNormMap K E ⁻¹' N := by
    ext c
    -- Compose subgroup membership directly; elaboration identifies the coerced set carriers.
    refine (mem_levelSubgroup (hF := hF)
      (N := (globalGroundOrderIso K N).toAddSubgroup) (c := c)).trans ?_
    rw [key]
    -- The additive subgroup is the underlying carrier of the ground-level integer submodule.
    change globalGroundEquiv K (.ofMul (ideleClassNormMap K E c)) ∈
      globalGroundOrderIso K N ↔ ideleClassNormMap K E c ∈ N
    rw [mem_globalGroundOrderIso, AddEquiv.symm_apply_apply, toMul_ofMul]
  rw [heq]
  exact hN.preimage (continuous_ideleClassNormMap K E)

/-! ### The Kummer case at every level -/

/-- **The Kummer case at a level.** If the fixed field `E` of an open subgroup `W` of `G_K`
contains the `p`-th roots of unity, then every open subgroup of the level of `W` containing the
`p`-th multiples contains the norm group of the level of an open subgroup of `W`. -/
private theorem exists_range_levelNorm_le_of_pow_mem {W : OpenSubgroup (AbsoluteGaloisGroup K)}
    {E : IntermediateField K (SeparableClosure K)} [NumberField E]
    (hE : fixedField W.toSubgroup = E) {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity E p]
    {N : AddSubgroup ((globalFormation K).level W)}
    (hN : IsOpen (levelSubgroup hE N : Set (IdeleClassGroup (𝓞 E) E)))
    (hp : ∀ a : (globalFormation K).level W, p • a ∈ N) :
    ∃ (W' : OpenSubgroup (AbsoluteGaloisGroup K)) (h : W' ≤ W),
      ((globalFormation K).levelNorm h).range ≤ N := by
  -- A finite extension `L/E` inside `Kˢ` whose norm group lies in the subgroup of `C_E`.
  obtain ⟨L, _, hL⟩ := exists_intermediateField_range_ideleClassNormMap_eq_of_pow_mem
    (Ω := SeparableClosure K) hN fun c ↦ by
      rw [mem_levelSubgroup, ofMul_pow, map_nsmul]
      exact hp _
  -- Read `L` as an intermediate field `L'` of `Kˢ/K` containing `E`. The two have the same
  -- elements, and `f` is the identity between them.
  let L' : IntermediateField K (SeparableClosure K) := L.restrictScalars K
  have hEL : E ≤ L' := fun x hx ↦ L.algebraMap_mem ⟨x, hx⟩
  let _ := (inclusion hEL).toRingHom.toAlgebra
  have : IsScalarTower E L' (SeparableClosure K) := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower K E L' := .of_algebraMap_eq fun _ ↦ rfl
  let f : L ≃ₐ[E] L' :=
    { toFun x := ⟨x, x.2⟩
      invFun x := ⟨x, x.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl
      map_add' _ _ := rfl
      commutes' _ := rfl }
  have : Module.Finite E L := .of_restrictScalars_finite ℚ E L
  have : Module.Finite E L' := .equiv f.toLinearEquiv
  have : Module.Finite K L' := .trans E L'
  have : NumberField L' := .of_module_finite K L'
  -- The open subgroup fixing `L'` lies in `W`, and its norm group is the norm group of `L/E`.
  let W' : OpenSubgroup (AbsoluteGaloisGroup K) :=
    ⟨L'.fixingSubgroup, L'.fixingSubgroup_isOpen⟩
  have hL' : fixedField W'.toSubgroup = L' := InfiniteGalois.fixedField_fixingSubgroup L'
  have hW' : W' ≤ W := OpenSubgroup.toSubgroup_le.1 <|
    (IntermediateField.fixingSubgroup_antitone hEL).trans
      (toSubgroup_eq_fixingSubgroup_of_fixedField_eq hE).ge
  refine ⟨W', hW', ?_⟩
  rw [range_ideleClassNormMap_eq_of_algEquiv f] at hL
  rintro _ ⟨a, rfl⟩
  obtain ⟨c, rfl⟩ := (ideleClassLevelEquiv hL').surjective a
  obtain ⟨c, rfl⟩ := Additive.ofMul.surjective c
  rw [levelNorm_ideleClassLevelEquiv hW' hE hL', ← mem_levelSubgroup]
  exact hL.le ⟨c, rfl⟩

/-- **The Kummer hypothesis of the induction on the index.** For every prime `p`, below every open
subgroup `W` of `G_K` lies an open subgroup `W'` over which every open subgroup of finite index of
the level containing the `p`-th multiples contains the norm group of the level of an open subgroup
of `W'`. -/
private theorem exists_le_forall_range_levelNorm_le (p : ℕ) (hp : p.Prime)
    (W : OpenSubgroup (AbsoluteGaloisGroup K)) :
    ∃ W' : OpenSubgroup (AbsoluteGaloisGroup K), W' ≤ W ∧
      ∀ N : AddSubgroup ((globalFormation K).level W'), IsOpenLevel W' N → N.FiniteIndex →
        (∀ a : (globalFormation K).level W', p • a ∈ N) →
          ∃ (W'' : OpenSubgroup (AbsoluteGaloisGroup K)) (h : W'' ≤ W'),
            ((globalFormation K).levelNorm h).range ≤ N := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨W', E, hW', hE, _, _⟩ := exists_le_hasEnoughRootsOfUnity p W
  have : NumberField E := .of_module_finite K E
  exact ⟨W', hW', fun N hN _ hpN ↦ exists_range_levelNorm_le_of_pow_mem hE (hN E hE) hpN⟩

/-! ### Global existence -/

/-- **Global existence** (Milne VII, Theorem 9.5). For a number field `K`, every open subgroup of
finite index of the idele class group `C_K` is the norm subgroup of a finite abelian extension of
`K`. -/
theorem globalAbelianExistence {N : Subgroup (IdeleClassGroup (𝓞 K) K)}
    (hN : IsOpen (N : Set (IdeleClassGroup (𝓞 K) K))) [N.FiniteIndex] :
    ∃ V : OpenNormalSubgroup (AbsoluteGaloisGroup K),
      V.IsAbelianClassFieldLayer ∧ globalNormSubgroup K V = N := by
  have hindex := index_globalGroundOrderIso K N
  have : (globalGroundOrderIso K N).toAddSubgroup.FiniteIndex :=
    ⟨hindex ▸ Subgroup.FiniteIndex.index_ne_zero⟩
  obtain ⟨V, hV, hVN⟩ :=
    (globalClassFormation K).exists_abelianLayer_normSubgroup_eq_of_forall_prime IsOpenLevel
      (fun hN h ↦ hN.mono h) (fun h _ hN ↦ hN.comap h) exists_le_forall_range_levelNorm_le
      (globalGroundOrderIso K N) (isOpenLevel_globalGroundOrderIso hN)
  refine ⟨V, hV, (globalGroundOrderIso K).injective ?_⟩
  rw [globalGroundOrderIso_globalNormSubgroup, hVN]

/-- **Global existence, forgetful form.** Every open subgroup of finite index of `C_K` is the norm
subgroup of some open normal subgroup of `G_K`, not necessarily an abelian layer. By norm
limitation, replacing a layer by its maximal abelian sublayer does not change its norm subgroup. -/
theorem globalExistence {N : Subgroup (IdeleClassGroup (𝓞 K) K)}
    (hN : IsOpen (N : Set (IdeleClassGroup (𝓞 K) K))) [N.FiniteIndex] :
    ∃ V : OpenNormalSubgroup (AbsoluteGaloisGroup K), globalNormSubgroup K V = N :=
  (globalAbelianExistence hN).imp fun _ h ↦ h.2

end TauCeti.ClassFieldTheory
