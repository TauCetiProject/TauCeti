/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Basic
public import TauCeti.NumberTheory.ModularForms.CharacterDecomp
public import TauCeti.NumberTheory.ModularForms.Newforms.Basic
public import TauCeti.NumberTheory.ModularForms.Petersson.Unitary

/-!
# The old and new subspaces at a fixed nebentypus

The old subspace `S_k(Γ₁(N))ᵒˡᵈ` and its Petersson-orthogonal complement, the new subspace
`S_k(Γ₁(N))ⁿᵉʷ` (`TauCeti/NumberTheory/ModularForms/Newforms/Basic.lean`), are both stable under
the diamond operators: the old one because the level-raising maps intertwine the diamonds, the
new one because the diamonds are Petersson-unitary
(`TauCeti/NumberTheory/ModularForms/Petersson/Unitary.lean`). Both therefore decompose along the
nebentypus character spaces `S_k(N, χ) = cuspFormCharSpace k χ`, and this file records what that
decomposition says about newness.

The main statement is the *refinement at a fixed nebentypus*: for a cusp form `f ∈ S_k(N, χ)`,
being new is orthogonality to the old forms **of the same nebentypus** alone,

`f ∈ S_k(Γ₁(N))ⁿᵉʷ ↔ f ⊥ (S_k(Γ₁(N))ᵒˡᵈ ⊓ S_k(N, χ))`,

because old forms of a different nebentypus are automatically orthogonal to `f`. Equivalently,
in the form Layer 3 of the ModularForms roadmap asks for, the new subspace of `S_k(N, χ)` —
the orthogonal complement, taken inside `S_k(N, χ)`, of the old forms there — is
`S_k(Γ₁(N))ⁿᵉʷ ⊓ S_k(N, χ)`: newness may be read at level `Γ₁(N)` and then intersected. The
old/new decomposition then restricts to each nebentypus space,
`S_k(N, χ) = S_k(N, χ)ᵒˡᵈ ⊕ S_k(N, χ)ⁿᵉʷ`.

The old part of `S_k(N, χ)` is then described by its generators: it is spanned by the
level-raises `V_d S_k(M, ψ)` from the proper divisor levels `M`, with `d * M ∣ N`, over the
characters `ψ` modulo `M` whose pull-back to level `N` is `χ`. Such a `ψ` exists exactly when the
conductor of `χ` divides `M`, and is then the descent `χ_M` of `χ`, so this is the description
`S_k(N, χ)ᵒˡᵈ = Σ_{M ∣ N, M ≠ N, cond χ ∣ M} Σ_{d ∣ N/M} V_d S_k(M, χ_M)`. The generators of
`S_k(Γ₁(N))ᵒˡᵈ` with any other nebentypus land in the other character spaces, which are
independent of `S_k(N, χ)`. In particular, when `χ` is primitive no proper divisor level carries
it, and every form in `S_k(N, χ)` is new.

## Main results

* `TauCeti.diamondOpCusp_mem_cuspFormsNew`: the new subspace is diamond-stable.
* `TauCeti.diamondOpCusp_mem_cuspFormsOldMultiples`: so is the refined old subspace of
  `TauCeti.cuspFormsOldMultiples`.
* `TauCeti.iSup_inf_cuspFormsOld_cuspFormCharSpace`,
  `TauCeti.iSup_inf_cuspFormsNew_cuspFormCharSpace`: the old and the new subspace are each the
  supremum of their nebentypus components.
* `TauCeti.mem_cuspFormsNew_iff_of_mem_cuspFormCharSpace`: a form of nebentypus `χ` is new
  exactly when it is orthogonal to the old forms of nebentypus `χ`.
* `TauCeti.cuspFormsNew_inf_cuspFormCharSpace`: `S_k(N, χ)ⁿᵉʷ = S_k(Γ₁(N))ⁿᵉʷ ⊓ S_k(N, χ)`.
* `TauCeti.sup_cuspFormsOld_cuspFormsNew_inf_cuspFormCharSpace` and
  `TauCeti.disjoint_cuspFormsOld_cuspFormsNew_inf_cuspFormCharSpace`: the old/new decomposition
  of `S_k(N, χ)`.
* `TauCeti.levelRaise_mem_cuspFormsOld_inf_cuspFormCharSpace` and
  `TauCeti.cuspFormsOld_inf_cuspFormCharSpace_le`: the introduction and elimination rules for the
  old part of `S_k(N, χ)`, whose generators are the level-raises of forms whose nebentypus pulls
  back to `χ`.
* `TauCeti.cuspFormsOld_inf_cuspFormCharSpace_eq_iSup`: the old part of `S_k(N, χ)` is the
  supremum of the images `V_d S_k(M, ψ)` over those generators.
* `TauCeti.cuspFormsOld_inf_cuspFormCharSpace_eq_bot_of_isPrimitive` and
  `TauCeti.cuspFormCharSpace_le_cuspFormsNew_of_isPrimitive`: for a primitive nebentypus there are
  no old forms, and `S_k(N, χ)` is new.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Section 5.6.
* Miyake, *Modular forms*, Section 4.6.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

open _root_.CuspForm

variable {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-! ### Diamond stability of the new subspace -/

/-- **The new subspace is diamond-stable.** The old subspace is carried onto itself by `⟨u⟩`,
and `⟨u⟩` is Petersson-unitary, so it preserves the orthogonal complement as well. -/
theorem diamondOpCusp_mem_cuspFormsNew (u : (ZMod N)ˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormsNew N k) :
    diamondOpCusp k u f ∈ cuspFormsNew N k := by
  rw [cuspFormsNew_def] at hf ⊢
  exact CuspForm.diamondOpCusp_mem_peterssonOrthogonal
    (fun _ _ hg ↦ diamondOpCusp_mem_cuspFormsOld _ hg) u hf

/-- **The refined old subspace is diamond-stable.** `⟨u⟩` sends a level-raised newform to the
level-raise of `⟨u'⟩` applied to it, where `u'` is the reduction of `u`; the new subspace at the
smaller level is itself diamond-stable, and the level condition `m ∣ M` is untouched. So the
generators are permuted among themselves. -/
theorem cuspFormsOldMultiples_map_diamondOpCusp_le (u : (ZMod N)ˣ) (m : ℕ) :
    (cuspFormsOldMultiples N k m).map (diamondOpCusp k u) ≤ cuspFormsOldMultiples N k m := by
  rw [Submodule.map_le_iff_le_comap]
  refine cuspFormsOldMultiples_le fun M d h hM hm g hg ↦ ?_
  have : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd h)
  have : NeZero M := NeZero.of_dvd (dvd_of_mul_left_dvd h)
  rw [Submodule.mem_comap, CuspForm.diamondOpCusp_levelRaise h]
  -- `levelRaiseₗ_apply` bridges the introduction rule's `levelRaiseₗ` to the bare `levelRaise`
  -- that `diamondOpCusp_levelRaise` produced above
  simpa only [CuspForm.levelRaiseₗ_apply] using
    levelRaise_mem_cuspFormsOldMultiples h hM hm k _ (diamondOpCusp_mem_cuspFormsNew _ hg)

/-- The refined old subspace is diamond-stable, in the membership form. -/
theorem diamondOpCusp_mem_cuspFormsOldMultiples (u : (ZMod N)ˣ) {m : ℕ}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormsOldMultiples N k m) :
    diamondOpCusp k u f ∈ cuspFormsOldMultiples N k m :=
  cuspFormsOldMultiples_map_diamondOpCusp_le u m (Submodule.mem_map_of_mem hf)

/-! ### The nebentypus components of the old and new subspaces -/

/-- **The old subspace is the sum of its nebentypus components.** -/
theorem iSup_inf_cuspFormsOld_cuspFormCharSpace (N : ℕ) [NeZero N] (k : ℤ) :
    (⨆ χ : (ZMod N)ˣ →* ℂˣ, cuspFormsOld N k ⊓ cuspFormCharSpace k χ) = cuspFormsOld N k :=
  iSup_inf_cuspFormCharSpace_of_invariant k _ fun _ _ hf ↦ by
    rw [diamondOpCuspHom_apply]; exact diamondOpCusp_mem_cuspFormsOld _ hf

/-- **The new subspace is the sum of its nebentypus components.** -/
theorem iSup_inf_cuspFormsNew_cuspFormCharSpace (N : ℕ) [NeZero N] (k : ℤ) :
    (⨆ χ : (ZMod N)ˣ →* ℂˣ, cuspFormsNew N k ⊓ cuspFormCharSpace k χ) = cuspFormsNew N k :=
  iSup_inf_cuspFormCharSpace_of_invariant k _ fun _ _ hf ↦ by
    rw [diamondOpCuspHom_apply]; exact diamondOpCusp_mem_cuspFormsNew _ hf

/-! ### Newness at a fixed nebentypus -/

/-- **Newness is tested against the old forms of the same nebentypus.** A cusp form of
nebentypus `χ` is new exactly when it is Petersson-orthogonal to the old forms of nebentypus
`χ`: the old subspace is the sum of its nebentypus components, and the components with
`ψ ≠ χ` are orthogonal to `f` for free, the nebentypus decomposition being an orthogonal one. -/
theorem mem_cuspFormsNew_iff_of_mem_cuspFormCharSpace
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    f ∈ cuspFormsNew N k ↔
      f ∈ CuspForm.peterssonOrthogonal (cuspFormsOld N k ⊓ cuspFormCharSpace k χ) := by
  have hold : CuspForm.peterssonOrthogonal (cuspFormsOld N k) =
      ⨅ ψ : (ZMod N)ˣ →* ℂˣ,
        CuspForm.peterssonOrthogonal (cuspFormsOld N k ⊓ cuspFormCharSpace k ψ) := by
    rw [← CuspForm.peterssonOrthogonal_iSup, iSup_inf_cuspFormsOld_cuspFormCharSpace]
  rw [cuspFormsNew_def, hold, Submodule.mem_iInf]
  refine ⟨fun h ↦ h χ, fun h ψ ↦ ?_⟩
  rcases eq_or_ne ψ χ with rfl | hψ
  · exact h
  · exact CuspForm.mem_peterssonOrthogonal_iff.mpr fun g hg ↦
      CuspForm.peterssonInnerCosets_eq_zero_of_mem_cuspFormCharSpace_of_ne hψ hg.2 hf

/-- **The new subspace of `S_k(N, χ)`.** The orthogonal complement of the old forms of
nebentypus `χ`, taken inside `S_k(N, χ)`, is what one gets by intersecting the new subspace of
`S_k(Γ₁(N))` with `S_k(N, χ)`: newness may be read at level `Γ₁(N)` and then restricted to a
nebentypus. This is the milestone `S_k(N, χ)ⁿᵉʷ = S_k(Γ₁(N))ⁿᵉʷ ⊓ S_k(N, χ)` of Layer 3 of the
ModularForms roadmap. -/
theorem cuspFormsNew_inf_cuspFormCharSpace (N : ℕ) [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    cuspFormsNew N k ⊓ cuspFormCharSpace k χ =
      CuspForm.peterssonOrthogonal (cuspFormsOld N k ⊓ cuspFormCharSpace k χ) ⊓
        cuspFormCharSpace k χ := by
  ext f
  simp only [Submodule.mem_inf]
  exact ⟨fun h ↦ ⟨(mem_cuspFormsNew_iff_of_mem_cuspFormCharSpace h.2).mp h.1, h.2⟩,
    fun h ↦ ⟨(mem_cuspFormsNew_iff_of_mem_cuspFormCharSpace h.2).mpr h.1, h.2⟩⟩

/-- **The old/new decomposition restricts to each nebentypus space**: `S_k(N, χ)` is spanned by
its old and its new part. Inside `S_k(N, χ)` the two are complementary, by the modular law and
the completeness of the Petersson-orthogonal complement. -/
theorem sup_cuspFormsOld_cuspFormsNew_inf_cuspFormCharSpace (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    cuspFormsOld N k ⊓ cuspFormCharSpace k χ ⊔ cuspFormsNew N k ⊓ cuspFormCharSpace k χ =
      cuspFormCharSpace k χ :=
  calc cuspFormsOld N k ⊓ cuspFormCharSpace k χ ⊔ cuspFormsNew N k ⊓ cuspFormCharSpace k χ
      = cuspFormsOld N k ⊓ cuspFormCharSpace k χ ⊔
          CuspForm.peterssonOrthogonal (cuspFormsOld N k ⊓ cuspFormCharSpace k χ) ⊓
            cuspFormCharSpace k χ := by
        rw [cuspFormsNew_inf_cuspFormCharSpace]
    _ = (cuspFormsOld N k ⊓ cuspFormCharSpace k χ ⊔
          CuspForm.peterssonOrthogonal (cuspFormsOld N k ⊓ cuspFormCharSpace k χ)) ⊓
            cuspFormCharSpace k χ := (sup_inf_assoc_of_le _ inf_le_right).symm
    _ = cuspFormCharSpace k χ := by
        rw [CuspForm.sup_peterssonOrthogonal_eq_top, top_inf_eq]

/-- **The old and new parts of `S_k(N, χ)` meet only in `0`.** -/
theorem disjoint_cuspFormsOld_cuspFormsNew_inf_cuspFormCharSpace (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    Disjoint (cuspFormsOld N k ⊓ cuspFormCharSpace k χ)
      (cuspFormsNew N k ⊓ cuspFormCharSpace k χ) :=
  (disjoint_cuspFormsOld_cuspFormsNew N k).mono inf_le_left inf_le_left

/-! ### The old part of `S_k(N, χ)` by nebentypus -/

/-- **Introduction rule for the old part of `S_k(N, χ)`.** The level-raise `V_d g` of a form
`g ∈ S_k(M, ψ)` of proper divisor level `M`, with `d * M ∣ N` and `χ` the pull-back of `ψ` along
`(ZMod N)ˣ → (ZMod M)ˣ`, is an old form of nebentypus `χ`. -/
theorem levelRaise_mem_cuspFormsOld_inf_cuspFormCharSpace {M d : ℕ} [NeZero d]
    (h : d * M ∣ N) (hM : M ≠ N) {ψ : (ZMod M)ˣ →* ℂˣ}
    (hχ : χ = ψ.comp (ZMod.unitsMap ((Dvd.intro_left d rfl).trans h)))
    {g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k} (hg : g ∈ cuspFormCharSpace k ψ) :
    CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) g ∈
      cuspFormsOld N k ⊓ cuspFormCharSpace k χ := by
  subst hχ
  exact ⟨levelRaise_mem_cuspFormsOld h hM k g,
    CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd h ψ hg⟩

/-- **Elimination rule for the old part of `S_k(N, χ)`.** A subspace containing every level-raise
`V_d g` of a form `g ∈ S_k(M, ψ)` of proper divisor level `M`, for every character `ψ` modulo `M`
whose pull-back to level `N` is `χ`, contains every old form of nebentypus `χ`.

Only the generators of the old subspace with the right nebentypus are tested: the old subspace is
spanned by the `V_d` images of the character spaces `S_k(M, ψ)`, the image of `S_k(M, ψ)` lies in
`S_k(N, ψ ∘ unitsMap)`, and the character spaces of `S_k(Γ₁(N))` are independent, so the generators
of any other nebentypus contribute nothing to `S_k(N, χ)`. -/
theorem cuspFormsOld_inf_cuspFormCharSpace_le
    {V : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)}
    (hV : ∀ (M d : ℕ) [NeZero d] (h : d * M ∣ N), M ≠ N →
      ∀ ψ : (ZMod M)ˣ →* ℂˣ, χ = ψ.comp (ZMod.unitsMap ((Dvd.intro_left d rfl).trans h)) →
        ∀ g ∈ cuspFormCharSpace k ψ,
          CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) g ∈ V) :
    cuspFormsOld N k ⊓ cuspFormCharSpace k χ ≤ V := by
  -- the old subspace lies in `(V ⊓ S_k(N, χ)) ⊔ ⨆_{χ' ≠ χ} S_k(N, χ')`
  set W := ⨆ (χ' : (ZMod N)ˣ →* ℂˣ) (_ : χ' ≠ χ), cuspFormCharSpace (N := N) k χ'
  have hold : cuspFormsOld N k ≤ V ⊓ cuspFormCharSpace k χ ⊔ W := by
    refine cuspFormsOld_le fun M d h hM f ↦ ?_
    have hMN : M ∣ N := (Dvd.intro_left d rfl).trans h
    have : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd h)
    -- split `f` along the character spaces at level `M`
    have hf : f ∈ ⨆ ψ : (ZMod M)ˣ →* ℂˣ, cuspFormCharSpace k ψ :=
      iSup_cuspFormCharSpace_eq_top (N := M) k ▸ Submodule.mem_top
    rw [← CuspForm.levelRaiseₗ_apply]
    refine Submodule.iSup_induction _
      (motive := fun g ↦ CuspForm.levelRaiseₗ d _ g ∈ V ⊓ cuspFormCharSpace k χ ⊔ W) hf
      (fun ψ g hg ↦ ?_) (by simp only [map_zero, zero_mem])
      fun x y hx hy ↦ by simpa only [map_add] using add_mem hx hy
    rw [CuspForm.levelRaiseₗ_apply]
    have hgχ := CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd h ψ hg
    by_cases hψ : ψ.comp (ZMod.unitsMap hMN) = χ
    · exact Submodule.mem_sup_left ⟨hV M d h hM ψ hψ.symm g hg, hψ ▸ hgχ⟩
    · exact Submodule.mem_sup_right
        (Submodule.mem_iSup_of_mem (ψ.comp (ZMod.unitsMap hMN)) (Submodule.mem_iSup_of_mem hψ hgχ))
  -- `W` meets `S_k(N, χ)` trivially, by the independence of the character spaces
  calc cuspFormsOld N k ⊓ cuspFormCharSpace k χ
      ≤ (V ⊓ cuspFormCharSpace k χ ⊔ W) ⊓ cuspFormCharSpace k χ := inf_le_inf_right _ hold
    _ = V ⊓ cuspFormCharSpace k χ := by
        rw [sup_inf_assoc_of_le _ inf_le_right, inf_comm W,
          (iSupIndep_cuspFormCharSpace k χ).eq_bot, sup_bot_eq]
    _ ≤ V := inf_le_left

/-- **The old part of `S_k(N, χ)` by nebentypus.** The old forms of nebentypus `χ` are exactly
the span of the level-raises `V_d S_k(M, ψ)` over the proper divisor levels `M` with
`d * M ∣ N` and the characters `ψ` modulo `M` pulling back to `χ`. Such a `ψ` is unique when it
exists, since `(ZMod N)ˣ → (ZMod M)ˣ` is onto, and it exists exactly when the Dirichlet character
of `χ` factors through `M`, that is, when its conductor divides `M`
(`DirichletCharacter.exists_eq_comp_unitsMap_of_factorsThrough`,
`DirichletCharacter.changeLevel_factorsThrough` and
`DirichletCharacter.mem_conductorSet_iff_conductor_dvd`). So this is the description
`S_k(N, χ)ᵒˡᵈ = Σ_{M ∣ N, M ≠ N, cond χ ∣ M} Σ_{d ∣ N / M} V_d S_k(M, χ_M)` of the old forms of
nebentypus `χ` by generators, as in Miyake, §4.6. -/
theorem cuspFormsOld_inf_cuspFormCharSpace_eq_iSup (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    cuspFormsOld N k ⊓ cuspFormCharSpace k χ =
      ⨆ (M : ℕ) (d : ℕ) (h : d * M ∣ N ∧ M ≠ N) (ψ : (ZMod M)ˣ →* ℂˣ)
        (_ : χ = ψ.comp (ZMod.unitsMap ((Dvd.intro_left d rfl).trans h.1))),
        haveI : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd h.1)
        (cuspFormCharSpace k ψ).map
          (CuspForm.levelRaiseₗ (k := k) d (Gamma1_map_le_conjAct_scaleGL_of_dvd h.1)) := by
  refine le_antisymm (cuspFormsOld_inf_cuspFormCharSpace_le fun M d _ h hM ψ hψ g hg ↦ ?_)
    (iSup_le fun M ↦ iSup_le fun d ↦ iSup_le fun h ↦ iSup_le fun ψ ↦ iSup_le fun hψ ↦ ?_)
  · rw [← CuspForm.levelRaiseₗ_apply]
    exact Submodule.mem_iSup_of_mem M <| Submodule.mem_iSup_of_mem d <|
      Submodule.mem_iSup_of_mem ⟨h, hM⟩ <| Submodule.mem_iSup_of_mem ψ <|
        Submodule.mem_iSup_of_mem hψ <| Submodule.mem_map_of_mem hg
  · have : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd h.1)
    rintro _ ⟨g, hg, rfl⟩
    rw [CuspForm.levelRaiseₗ_apply]
    exact levelRaise_mem_cuspFormsOld_inf_cuspFormCharSpace h.1 h.2 hψ hg

/-- **A primitive nebentypus has no old forms.** If the Dirichlet character of `χ` is primitive
of conductor `N`, it is pulled back from no proper divisor level, so `S_k(N, χ)` contains no old
form. -/
theorem cuspFormsOld_inf_cuspFormCharSpace_eq_bot_of_isPrimitive
    (hχ : DirichletCharacter.IsPrimitive (MulChar.ofUnitHom χ : DirichletCharacter ℂ N)) :
    cuspFormsOld N k ⊓ cuspFormCharSpace k χ = ⊥ := by
  refine le_bot_iff.mp <| cuspFormsOld_inf_cuspFormCharSpace_le fun M d _ h hM ψ hψ _ _ ↦ ?_
  have hMN : M ∣ N := (Dvd.intro_left d rfl).trans h
  -- the conductor `N` of `χ` divides the level `M` it is pulled back from
  have hcond : DirichletCharacter.conductor (MulChar.ofUnitHom χ : DirichletCharacter ℂ N) ∣ M :=
    DirichletCharacter.conductor_dvd_of_mem_conductorSet _ <| by
      simpa only [DirichletCharacter.mem_conductorSet_iff, DirichletCharacter.changeLevel_def,
        MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq, Equiv.apply_symm_apply, ← hψ] using
        DirichletCharacter.changeLevel_factorsThrough (MulChar.ofUnitHom ψ) hMN
  rw [hχ] at hcond
  exact absurd (Nat.dvd_antisymm hMN hcond) hM

/-- **Every form of primitive nebentypus is new.** If the Dirichlet character of `χ` is primitive
of conductor `N`, then `S_k(N, χ) ≤ S_k(Γ₁(N))ⁿᵉʷ`: the old part of `S_k(N, χ)` vanishes
(`cuspFormsOld_inf_cuspFormCharSpace_eq_bot_of_isPrimitive`), and `S_k(N, χ)` is the sum of its
old and new parts. -/
theorem cuspFormCharSpace_le_cuspFormsNew_of_isPrimitive
    (hχ : DirichletCharacter.IsPrimitive (MulChar.ofUnitHom χ : DirichletCharacter ℂ N)) :
    cuspFormCharSpace k χ ≤ cuspFormsNew N k := by
  rw [← sup_cuspFormsOld_cuspFormsNew_inf_cuspFormCharSpace N k χ,
    cuspFormsOld_inf_cuspFormCharSpace_eq_bot_of_isPrimitive hχ, bot_sup_eq]
  exact inf_le_left

end TauCeti
