/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.FiniteType
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Kernels

/-!
# Extending quasi-coherent modules along quasi-compact open immersions

Let `j : U ⟶ X` be a quasi-compact open immersion. Every quasi-coherent `𝒪_U`-module `F` is the
restriction of a quasi-coherent `𝒪_X`-module, namely of `j_* F`: an open immersion is separated,
hence quasi-separated, so `j_* F` is quasi-coherent, and the counit `j^* j_* F ⟶ F` of the
restriction--pushforward adjunction is an isomorphism. Likewise every quasi-coherent submodule
`F ⊆ j^* G` of the restriction of a quasi-coherent `G` is the restriction of a quasi-coherent
submodule of `G`: the kernel of `G ⟶ j_* j^* G ⟶ j_* (j^* G / F)`. This extension changes
nothing away from where `F` is a proper submodule: on an open `V ⊆ X` over whose preimage `F` is
all of `j^* G`, the extension is all of `G`, because `j_* (j^* G / F)` vanishes on `V`.

When `X` is moreover quasi-compact and quasi-separated, finite type is preserved too: a
finite-type quasi-coherent submodule of `j^* G` is the restriction of a finite-type
quasi-coherent submodule of `G`, and consequently a finite-type quasi-coherent `𝒪_U`-module is the
restriction of a finite-type quasi-coherent `𝒪_X`-module. The key step says that a quasi-coherent
`𝒪_X`-module `N` of finite type over a quasi-compact open `V` has a finite-type quasi-coherent
submodule that is all of `N` over `V`. It is proved by covering `X` with finitely many affine opens
and enlarging `V` by one affine open `W` at a time: on the affine scheme `W`, some finite-type
quasi-coherent submodule of `N|_W` is everything over the quasi-compact open `V ∩ W`, and its
extension to a submodule of `N` changes nothing over `V` and is of finite type over `V ∪ W`.

Submodules are monomorphisms in the abelian category of `𝒪_X`-modules.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.exists_isQuasicoherent_restrict_iso`: every quasi-coherent
  module on `U` is the restriction of a quasi-coherent module on `X`.
* `AlgebraicGeometry.Scheme.Modules.exists_mono_restrict_iso_of_isQuasicoherent`: every
  quasi-coherent submodule of `j^* G` is the restriction of a quasi-coherent submodule of `G`.
* `AlgebraicGeometry.Scheme.Modules.exists_isFiniteType_mono_isIso_restrict_of_quasiSeparatedSpace`:
  on a quasi-compact quasi-separated scheme, a quasi-coherent module of finite type over a
  quasi-compact open has a finite-type quasi-coherent submodule that is everything over that open.
* `AlgebraicGeometry.Scheme.Modules.exists_mono_restrict_iso_of_isFiniteType`: on a
  quasi-compact quasi-separated scheme, every finite-type quasi-coherent submodule of `j^* G` is
  the restriction of a finite-type quasi-coherent submodule of `G`.
* `AlgebraicGeometry.Scheme.Modules.exists_isFiniteType_restrict_iso`: on a quasi-compact
  quasi-separated scheme, every finite-type quasi-coherent module on `U` is the restriction of a
  finite-type quasi-coherent module on `X`.

## References

* The Stacks Project, Lemma 28.23.1 (Tag 01PE), Lemma 28.23.2 (Tag 01PF) and
  Lemma 28.23.5 (Tag 0G41), part (1).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **Extension of quasi-coherent modules.** Along a quasi-compact open immersion `j : U ⟶ X`,
every quasi-coherent `𝒪_U`-module `F` is `j^* G` for a quasi-coherent `𝒪_X`-module `G`, namely
`G = j_* F`. Stacks, Lemma 28.23.1 (01PE), part (1). -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_isQuasicoherent_restrict_iso
    [QuasiCompact j] (F : U.Modules) [F.IsQuasicoherent] :
    ∃ (G : X.Modules) (_ : G.IsQuasicoherent), Nonempty (G.restrict j ≅ F) :=
  ⟨_, inferInstance, ⟨(Scheme.Modules.restrictFunctorAdjCounitIso j).app F⟩⟩

/-- **Extension of quasi-coherent submodules.** Along a quasi-compact open immersion
`j : U ⟶ X`, let `G` be a quasi-coherent `𝒪_X`-module and `i : F ⟶ j^* G` a quasi-coherent
submodule. Then `F` is the restriction of a quasi-coherent submodule `i' : G' ⟶ G`: there is an
isomorphism `j^* G' ≅ F` carrying `j^* i'` to `i`. The module `G'` is the kernel of the
composite `G ⟶ j_* j^* G ⟶ j_* (j^* G / F)`. Moreover `i'` is an isomorphism over every open
`V ⊆ X` such that `i` is an isomorphism over `j⁻¹ V`. Stacks, Lemma 28.23.1 (01PE), part (2). -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_mono_restrict_iso_of_isQuasicoherent
    [QuasiCompact j] {G : X.Modules} [G.IsQuasicoherent] {F : U.Modules} [F.IsQuasicoherent]
    (i : F ⟶ G.restrict j) [Mono i] :
    ∃ (G' : X.Modules) (_ : G'.IsQuasicoherent) (i' : G' ⟶ G) (_ : Mono i')
      (e : G'.restrict j ≅ F), (Scheme.Modules.restrictFunctor j).map i' = e.hom ≫ i ∧
        ∀ V : X.Opens, IsIso ((Scheme.Modules.restrictFunctor (j ⁻¹ᵁ V).ι).map i) →
          IsIso ((Scheme.Modules.restrictFunctor V.ι).map i') := by
  let R := Scheme.Modules.restrictFunctor j
  let adj := Scheme.Modules.restrictAdjunction j
  let φ : G ⟶ (Scheme.Modules.pushforward j).obj (cokernel i) :=
    adj.homEquiv _ _ (cokernel.π i)
  -- On `U`, `φ` is the cokernel projection of `i` followed by the inverse counit.
  have hφ : R.map φ = cokernel.π i ≫ inv (adj.counit.app (cokernel i)) := by
    rw [IsIso.eq_comp_inv, ← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]
  have hi : IsLimit (KernelFork.ofι i (by rw [hφ, cokernel.condition_assoc, zero_comp]) :
      KernelFork (R.map φ)) :=
    isKernelCompMono (Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel i)) _ hφ
  -- `j^*` preserves the kernel of `φ`, which is therefore carried to `i`.
  let e : (kernel φ).restrict j ≅ F :=
    PreservesKernel.iso R φ ≪≫ (kernelIsKernel (R.map φ)).conePointUniqueUpToIso hi
  refine ⟨kernel φ, inferInstance, kernel.ι φ, inferInstance, e, ?_, fun V hV ↦ ?_⟩
  · have h : ((kernelIsKernel (R.map φ)).conePointUniqueUpToIso hi).hom ≫ i = kernel.ι _ :=
      (kernelIsKernel (R.map φ)).conePointUniqueUpToIso_hom_comp hi WalkingParallelPair.zero
    simp [e, h, R]
  -- Over `j⁻¹ V` the cokernel of `i` vanishes, hence so does `j_* (cokernel i)` over `V`.
  let R' := Scheme.Modules.restrictFunctor (j ⁻¹ᵁ V).ι
  let RV := Scheme.Modules.restrictFunctor V.ι
  have hQ : IsZero ((cokernel i).restrict (j ⁻¹ᵁ V).ι) :=
    (isZero_cokernel_of_epi (R'.map i)).of_iso (PreservesCokernel.iso R' i)
  have hP : IsZero (((Scheme.Modules.pushforward j).obj (cokernel i)).restrict V.ι) :=
    ((Scheme.Modules.pushforward (j ∣_ V)).map_isZero hQ).of_iso
      ((restrictPushforwardIso j V).app (cokernel i))
  have := kernel.ι_of_zero (hP.eq_of_tgt (RV.map φ) 0)
  rw [← kernelComparison_comp_ι φ RV, ← PreservesKernel.iso_hom]
  infer_instance

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}}

/-- One step of the extension of finite-type submodules: let `N` be a quasi-coherent module of
finite type over a quasi-compact open `V` of a quasi-separated scheme, and `W` an affine open. Then
`N` has a quasi-coherent submodule which is everything over `V` and of finite type over `V ⊔ W`. -/
private theorem exists_mono_isIso_restrict_isFiniteType_restrict_sup [QuasiSeparatedSpace X]
    {N : X.Modules} [N.IsQuasicoherent] {V : X.Opens}
    (hV : IsCompact (V : Set X)) [(N.restrict V.ι).IsFiniteType] {W : X.Opens}
    (hW : IsAffineOpen W) :
    ∃ (N' : X.Modules) (_ : N'.IsQuasicoherent) (i : N' ⟶ N) (_ : Mono i),
      IsIso ((restrictFunctor V.ι).map i) ∧
        (N'.restrict (V ⊔ W).ι).IsFiniteType := by
  have : IsAffine W := hW
  -- On the affine scheme `W`, find a finite-type submodule of `N|_W` that is everything over
  -- the quasi-compact open `V ∩ W`.
  let O : W.toScheme.Opens := W.ι ⁻¹ᵁ V
  have : ((N.restrict W.ι).restrict O.ι).IsFiniteType := by
    have : (N.restrict (O.ι ≫ W.ι)).IsFiniteType := by
      refine isFiniteType_restrict_of_opensRange_le V.ι _ ?_ N
      rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
        Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        Scheme.Opens.opensRange_ι]
      exact inf_le_right
    exact SheafOfModules.IsFiniteType.of_iso (R := O.toScheme.ringCatSheaf)
      ((restrictFunctorComp O.ι W.ι).app N)
  obtain ⟨H, _, _, h, _, hh⟩ :=
    exists_isFiniteType_mono_isIso_restrict (N := N.restrict W.ι) O
      (W.ι.isCompact_preimage hV)
  -- Its extension to `X` is everything over `V`, and of finite type over `V` and over `W`.
  obtain ⟨N', _, i, _, e, -, hi⟩ := exists_mono_restrict_iso_of_isQuasicoherent W.ι h
  have := hi V hh
  refine ⟨N', inferInstance, i, inferInstance, this, ?_⟩
  rw [sup_eq_iSup]
  refine isFiniteType_restrict_iSup _ _ fun b ↦ ?_
  cases b
  · exact SheafOfModules.IsFiniteType.of_iso (R := W.toScheme.ringCatSheaf) e.symm
  · exact SheafOfModules.IsFiniteType.of_iso (R := V.toScheme.ringCatSheaf)
      (asIso ((restrictFunctor V.ι).map i)).symm

/-- **Finite-type submodules over a quasi-compact open.** Let `X` be a quasi-compact
quasi-separated scheme, `N` a quasi-coherent `𝒪_X`-module and `V ⊆ X` a quasi-compact open such
that `N|_V` is of finite type. Then there is a finite-type quasi-coherent submodule `i : N' ⟶ N`
that is an isomorphism over `V`. -/
theorem exists_isFiniteType_mono_isIso_restrict_of_quasiSeparatedSpace [CompactSpace X]
    [QuasiSeparatedSpace X] {N : X.Modules} [N.IsQuasicoherent]
    (V : X.Opens) (hV : IsCompact (V : Set X)) [(N.restrict V.ι).IsFiniteType] :
    ∃ (N' : X.Modules) (_ : N'.IsQuasicoherent) (_ : N'.IsFiniteType) (i : N' ⟶ N) (_ : Mono i),
      IsIso ((restrictFunctor V.ι).map i) := by
  classical
  let V' (t : Finset X.affineOpens) : X.Opens := V ⊔ t.sup fun W ↦ W.1
  -- Enlarge `V` by finitely many affine opens, one at a time.
  have key (t : Finset X.affineOpens) : IsCompact (V' t : Set X) ∧
      ∃ (N' : X.Modules) (_ : N'.IsQuasicoherent) (i : N' ⟶ N) (_ : Mono i),
        IsIso ((restrictFunctor V.ι).map i) ∧
          (N'.restrict (V' t).ι).IsFiniteType := by
    induction t using Finset.induction_on with
    | empty =>
      have h : V' ∅ = V := by simp [V']
      refine ⟨h ▸ hV, N, inferInstance, 𝟙 N, inferInstance, inferInstance, ?_⟩
      rw [h]
      infer_instance
    | insert W t _ ih =>
      obtain ⟨hc, N₁, _, i₁, _, hi₁, _⟩ := ih
      have hV' : V' (insert W t) = V' t ⊔ W.1 := by
        simp only [V', Finset.sup_insert]
        ac_rfl
      obtain ⟨N₂, _, i₂, _, hi₂, _⟩ :=
        exists_mono_isIso_restrict_isFiniteType_restrict_sup (N := N₁) hc W.2
      have : IsIso ((restrictFunctor V.ι).map i₂) :=
        isIso_restrictFunctor_map_of_opensRange_le (V' t).ι V.ι (by simp [V']) i₂
      refine ⟨hV' ▸ hc.union W.2.isCompact, N₂, inferInstance, i₂ ≫ i₁, inferInstance, ?_,
        hV' ▸ ‹_›⟩
      rw [Functor.map_comp]
      infer_instance
  -- Finitely many affine opens cover `X`.
  obtain ⟨s, _, -, hs⟩ := X.exists_finite_affineOpens_cover (U := ⊤) (by simp [isCompact_univ])
  let t := (Set.toFinite s).toFinset
  have ht : V' t = ⊤ := eq_top_iff.mpr <| hs.trans <| iSup_le fun W ↦
    le_sup_of_le_right (Finset.le_sup (f := fun W : X.affineOpens ↦ W.1)
      ((Set.toFinite s).mem_toFinset.mpr W.2))
  obtain ⟨-, N', _, i, _, hi, _⟩ := key t
  exact ⟨N', inferInstance, TauCeti.AlgebraicGeometry.isFiniteType_of_isFiniteType_restrict N'
    (fun _ : Unit ↦ V' t) (by simp [ht]) fun _ ↦ ‹_›, i, inferInstance, hi⟩

/-- **Extension of finite-type quasi-coherent submodules.** Let `X` be a quasi-compact
quasi-separated scheme, `j : U ⟶ X` a quasi-compact open immersion, `G` a quasi-coherent
`𝒪_X`-module and `i : F ⟶ j^* G` a finite-type quasi-coherent submodule. Then `F` is the
restriction of a finite-type quasi-coherent submodule `i' : G' ⟶ G`: there is an isomorphism
`j^* G' ≅ F` carrying `j^* i'` to `i`. Stacks, Lemma 28.23.2 (01PF). -/
theorem exists_mono_restrict_iso_of_isFiniteType
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [CompactSpace X] [QuasiSeparatedSpace X]
    {G : X.Modules} [G.IsQuasicoherent] {F : U.Modules} [F.IsQuasicoherent] [F.IsFiniteType]
    (i : F ⟶ G.restrict j) [Mono i] :
    ∃ (G' : X.Modules) (_ : G'.IsQuasicoherent) (_ : G'.IsFiniteType) (i' : G' ⟶ G) (_ : Mono i')
      (e : G'.restrict j ≅ F), (restrictFunctor j).map i' = e.hom ≫ i := by
  -- First extend `F` to a quasi-coherent submodule `G₀` of `G`, which is of finite type over `U`.
  obtain ⟨G₀, _, i₀, _, e₀, he₀, -⟩ := exists_mono_restrict_iso_of_isQuasicoherent j i
  have : (G₀.restrict j).IsFiniteType :=
    SheafOfModules.IsFiniteType.of_iso (R := U.ringCatSheaf) e₀.symm
  have : (G₀.restrict j.opensRange.ι).IsFiniteType :=
    isFiniteType_restrict_of_opensRange_le j j.opensRange.ι (by simp) G₀
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace j
  -- Then shrink `G₀` to a finite-type submodule which is still all of `G₀` over `U`.
  obtain ⟨G', _, _, i', _, hi'⟩ :=
    exists_isFiniteType_mono_isIso_restrict_of_quasiSeparatedSpace (N := G₀) j.opensRange
      (by simpa using isCompact_range j.continuous)
  have : IsIso ((restrictFunctor j).map i') :=
    isIso_restrictFunctor_map_of_opensRange_le j.opensRange.ι j (by simp) i'
  refine ⟨G', inferInstance, inferInstance, i' ≫ i₀, inferInstance,
    asIso ((restrictFunctor j).map i') ≪≫ e₀, ?_⟩
  simp [he₀]

/-- **Extension of finite-type quasi-coherent modules.** Along a quasi-compact open immersion
`j : U ⟶ X` into a quasi-compact quasi-separated scheme, every finite-type quasi-coherent
`𝒪_U`-module `F` is `j^* G` for a finite-type quasi-coherent `𝒪_X`-module `G`.
Stacks, Lemma 28.23.5 (0G41), part (1). -/
theorem exists_isFiniteType_restrict_iso
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [CompactSpace X] [QuasiSeparatedSpace X]
    (F : U.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ (G : X.Modules) (_ : G.IsQuasicoherent) (_ : G.IsFiniteType), Nonempty (G.restrict j ≅ F) :=
  -- `F` is a finite-type submodule of `j^* j_* F`, with `j_* F` quasi-coherent.
  have ⟨G, hG, hG', _, _, e, _⟩ := exists_mono_restrict_iso_of_isFiniteType j
    (F := F) ((restrictFunctorAdjCounitIso j).app F).inv
  ⟨G, hG, hG', ⟨e⟩⟩

end AlgebraicGeometry.Scheme.Modules
