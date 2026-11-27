/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.AlgebraicGeometry.Sites.Etale.FiniteLisse.Kernels
public import TauCeti.CategoryTheory.Exact.Abelian
public import TauCeti.CategoryTheory.Sites.Grothendieck
public import TauCeti.CategoryTheory.Sites.Limits

/-!
# Finite lisse étale sheaves form a weak Serre class

Let `S` be a scheme and `Λ` a ring. This file proves that finite lisse étale sheaves of
`Λ`-modules on `S` (`CategoryTheory.Sheaf.IsFiniteLisse`) are closed under cokernels over any ring
`Λ`, and closed under kernels and extensions when `Λ` is left Noetherian: together with
`CategoryTheory.Sheaf.containsZero_isFiniteLisse` and closure under isomorphisms, they form a weak
Serre class in `Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)`.

Closure under cokernels and kernels comes from `CategoryTheory.Sheaf.IsFiniteLisse.cokernel` and
`CategoryTheory.Sheaf.IsFiniteLisse.kernel` in
`TauCeti.AlgebraicGeometry.Sites.Etale.FiniteLisse.Kernels`.

For an extension `0 ⟶ F ⟶ E ⟶ G ⟶ 0` with `F` and `G` finite lisse over left Noetherian `Λ`,
pass to a common trivializing étale cover so `F` and `G` are constant on finitely generated modules
`M` and `N`. Choose a finite presentation `0 ⟶ K ⟶ Λ^a ⟶ N ⟶ 0` (whose kernel `K` is finitely
generated since `Λ` is left Noetherian); lift the basis of `Λ^a` étale-locally to `E`, factor the
induced map on `const K` locally through a linear map `g : K ⟶ M` using
`CategoryTheory.Sheaf.exists_mem_overPullback_map_eq_of_iso`, and push out `K ⟶ Λ^a` along `g`
to obtain a finitely generated module `P` whose constant sheaf maps isomorphically to `E` by the
short five lemma.

## Main results

* `CategoryTheory.Sheaf.isClosedUnderCokernels_isFiniteLisse`: finite lisse sheaves are closed under
  cokernels over any ring `Λ`.
* `CategoryTheory.Sheaf.isClosedUnderKernels_isFiniteLisse`: finite lisse sheaves are closed under
  kernels over any left Noetherian ring `Λ`.
* `CategoryTheory.Sheaf.isClosedUnderExtensions_isFiniteLisse`: finite lisse sheaves are closed
  under extensions over any left Noetherian ring `Λ`.
* `CategoryTheory.Sheaf.IsFiniteLisse.of_shortExact`: dot-notation form for extensions.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IX, §2.7.
* The Stacks Project, Section 59.64 and Section 59.71, Tag 03RZ.
-/

public section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry Scheme

namespace CategoryTheory.Sheaf

section Helpers

/-- Refining a jointly surjective family `u : ∀ i, U i ⟶ S` by jointly surjective families
`v i : ∀ k, V i k ⟶ U i` yields a jointly surjective `Σ`-indexed family. -/
private lemma iUnion_range_comp_sigma {S : Scheme.{u}} {ι : Type*} {U : ι → Scheme.{u}}
    {u : ∀ i, U i ⟶ S} (hu : ⋃ i, Set.range (u i) = .univ)
    {κ : ι → Type*} {V : ∀ i, κ i → Scheme.{u}}
    {v : ∀ i, ∀ k : κ i, V i k ⟶ U i} (hv : ∀ i, ⋃ k, Set.range (v i k) = .univ) :
    (⋃ p : Σ i, κ i, Set.range (v p.1 p.2 ≫ u p.1)) = .univ := by
  refine Set.eq_univ_of_forall fun s ↦ ?_
  obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.mp (hu ▸ Set.mem_univ s)
  obtain ⟨k, z, rfl⟩ := Set.mem_iUnion.mp (hv i ▸ Set.mem_univ x)
  exact Set.mem_iUnion.mpr ⟨⟨i, k⟩, z, Scheme.Hom.comp_apply (v i k) (u i) z⟩

/-- Transporting a short exact sequence along small étale pullback and outer isomorphisms preserves
short exactness. -/
private lemma shortExact_pullback_outerIso {Λ : Type u} [Ring Λ] {X Y : Scheme.{u}}
    (u : X ⟶ Y) {T : ShortComplex (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))}
    (hT : T.ShortExact) {C₁ C₃ : Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ)}
    (e₁ : (u.smallEtalePullback (ModuleCat.{u} Λ)).obj T.X₁ ≅ C₁)
    (e₃ : (u.smallEtalePullback (ModuleCat.{u} Λ)).obj T.X₃ ≅ C₃) :
    (ShortComplex.mk
      (e₁.inv ≫ (u.smallEtalePullback (ModuleCat.{u} Λ)).map T.f)
      ((u.smallEtalePullback (ModuleCat.{u} Λ)).map T.g ≫ e₃.hom)
      (by rw [Category.assoc, ← Category.assoc ((u.smallEtalePullback (ModuleCat.{u} Λ)).map T.f),
        ← Functor.map_comp, T.zero, Functor.map_zero, zero_comp, comp_zero])).ShortExact := by
  refine ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (S₁ := T.map (u.smallEtalePullback (ModuleCat.{u} Λ)))
      e₁ (Iso.refl _) e₃ ?_ ?_)
    (Hom.shortExact_map_smallEtalePullback u hT) <;> simp

/-- Any morphism `φ : const M ⟶ const N` of constant étale sheaves of `Λ`-modules on `S` with
`M` finitely generated comes étale-locally from a constant `Λ`-linear map `M ⟶ N`. -/
private theorem exists_etaleCover_map_constantSheaf {S : Scheme.{u}} {Λ : Type u} [Ring Λ]
    {M N : ModuleCat.{u} Λ} [Module.Finite Λ M]
    (φ : (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj M ⟶
      (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj N) :
    ∃ (ι : Type u) (U : ι → Scheme.{u}) (u : ∀ i, U i ⟶ S) (_ : ∀ i, Etale (u i)),
      (⋃ i, Set.range (u i) = .univ) ∧
        ∀ i, ∃ f : M ⟶ N,
          ((u i).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) M).inv ≫
            ((u i).smallEtalePullback (ModuleCat.{u} Λ)).map φ ≫
            ((u i).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) N).hom =
              (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).map f := by
  obtain ⟨R, hR, hRg⟩ := exists_mem_overPullback_map_eq_of_iso (J := smallEtaleTopology S)
    φ (Y := Etale.mk (𝟙 S)) (Iso.refl _) (Iso.refl _)
  obtain ⟨ι, U, u, hu_et, _, hgR, hcov⟩ := exists_etaleCover_of_mem_smallEtaleTopology_terminal hR
  refine ⟨ι, U, u, hu_et, hcov, fun i ↦ ?_⟩
  have := hu_et i
  obtain ⟨gi, hgi⟩ := hgR i
  obtain ⟨f, hf⟩ := hRg gi hgi
  have hrefl (G : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)) :
      (overIsoRestrict (Iso.refl (G.over (Etale.mk (𝟙 S)))) gi).hom = 𝟙 _ := by
    ext W : 3
    exact (overIsoRestrict_hom_hom_app (Iso.refl _) gi W).trans rfl
  rw [hrefl, hrefl, Category.comp_id, Category.id_comp] at hf
  let e := (Etale.mk (u i)).smallEtalePullbackIsoOver (ModuleCat.{u} Λ)
  have hpb : ((u i).smallEtalePullback (ModuleCat.{u} Λ)).map φ =
      ((u i).smallEtalePullback (ModuleCat.{u} Λ)).map
        ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).map f) := by
    have h₁ := e.hom.naturality φ
    have h₂ := e.hom.naturality ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).map f)
    have h₃ : (((Etale.mk (u i)).overSheafEquiv (ModuleCat.{u} Λ)).functor.map
        (((smallEtaleTopology S).overPullback (ModuleCat.{u} Λ) (Etale.mk (u i))).map φ)) =
        (((Etale.mk (u i)).overSheafEquiv (ModuleCat.{u} Λ)).functor.map
          (((smallEtaleTopology S).overPullback (ModuleCat.{u} Λ) (Etale.mk (u i))).map
            ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).map f))) :=
      congrArg ((Etale.mk (u i)).overSheafEquiv (ModuleCat.{u} Λ)).functor.map hf
    have heq := (h₁.trans (congrArg (e.hom.app _ ≫ ·) h₃)).trans h₂.symm
    exact (cancel_mono (e.hom.app _)).1 heq
  refine ⟨f, ?_⟩
  rw [hpb]
  dsimp only [Hom.smallEtalePullbackConstantSheafIso, Hom.smallEtalePullback]
  rw [← Category.assoc, ← Functor.sheafPullbackConstantSheafIso_inv_naturality, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end Helpers

section Closure

variable {S : Scheme.{u}} {Λ : Type u} [Ring Λ]

/-- Given two finite lisse sheaves `F` and `G` on `S`, there exists a `Type u`-indexed jointly
surjective étale cover of `S` over each piece of which both `F` and `G` become isomorphic to
constant sheaves on finitely generated `Λ`-modules. -/
private theorem exists_etaleCover_pair_constantSheaf
    {F G : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    (hF : F.IsFiniteLisse) (hG : G.IsFiniteLisse) :
    ∃ (ι : Type u) (U : ι → Scheme.{u}) (u : ∀ i, U i ⟶ S) (_ : ∀ i, Etale (u i)),
      (⋃ i, Set.range (u i) = .univ) ∧
        ∀ i, ∃ M N : ModuleCat.{u} Λ, Module.Finite Λ M ∧ Module.Finite Λ N ∧
          Nonempty (((u i).smallEtalePullback (ModuleCat.{u} Λ)).obj F ≅
            (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).obj M) ∧
          Nonempty (((u i).smallEtalePullback (ModuleCat.{u} Λ)).obj G ≅
            (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).obj N) := by
  obtain ⟨ι, U, u, hu_et, hu_cov, htrivF⟩ := (isFiniteLisse_iff F).mp hF
  choose κ V v hv_et hv_cov htrivG using fun i ↦
    (isFiniteLisse_iff (((u i).smallEtalePullback (ModuleCat.{u} Λ)).obj G)).mp
      (hG.smallEtalePullback (u i))
  refine ⟨Σ i, κ i, fun p ↦ V p.1 p.2, fun p ↦ v p.1 p.2 ≫ u p.1,
    fun p ↦ have := hu_et p.1; have := hv_et p.1 p.2; inferInstance,
    iUnion_range_comp_sigma hu_cov hv_cov, fun p ↦ ?_⟩
  obtain ⟨M, hM, ⟨eF⟩⟩ := htrivF p.1
  obtain ⟨N, hN, ⟨eG⟩⟩ := htrivG p.1 p.2
  have hcompF := (Hom.smallEtalePullbackComp (v p.1 p.2) (u p.1) (ModuleCat.{u} Λ)).app F
  have hcompG := (Hom.smallEtalePullbackComp (v p.1 p.2) (u p.1) (ModuleCat.{u} Λ)).app G
  exact ⟨M, N, hM, hN,
    ⟨hcompF ≪≫ ((v p.1 p.2).smallEtalePullback (ModuleCat.{u} Λ)).mapIso eF ≪≫
      (v p.1 p.2).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) M⟩,
    ⟨hcompG ≪≫ eG⟩⟩

/-- Over any ring `Λ`, finite lisse étale sheaves of `Λ`-modules are closed under cokernels. -/
instance isClosedUnderCokernels_isFiniteLisse :
    ObjectProperty.IsClosedUnderCokernels
      (IsFiniteLisse : ObjectProperty (Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))) where
  cokernels_le := by
    rintro _ ⟨φ, k, hk, hF, hG⟩
    exact (hF.cokernel hG φ).of_iso (hk.coconePointUniqueUpToIso (cokernelIsCokernel φ)).symm

/-- Over a left Noetherian ring `Λ`, finite lisse étale sheaves of `Λ`-modules are closed under
kernels. -/
instance isClosedUnderKernels_isFiniteLisse [IsNoetherianRing Λ] :
    ObjectProperty.IsClosedUnderKernels
      (IsFiniteLisse : ObjectProperty (Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))) where
  kernels_le := by
    rintro _ ⟨φ, k, hk, hF, hG⟩
    exact (hF.kernel hG φ).of_iso (hk.conePointUniqueUpToIso (kernelIsKernel φ)).symm

/-- Given an epimorphism `g : E ⟶ const N` and a linear map `πN : Λ^a ⟶ N`, there exists an étale
cover of `S` over each piece of which `πN` lifts along the pullback of `g` to `const (Λ^a) ⟶ u^* E`.
-/
private theorem exists_etaleCover_lift_constantSheaf_free
    {S : Scheme.{u}} {N : ModuleCat.{u} Λ} {a : ℕ}
    {E : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    (g : E ⟶ (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj N) [Epi g]
    (πN : ModuleCat.of Λ (Fin a → Λ) ⟶ N) :
    ∃ (ι : Type u) (U : ι → Scheme.{u}) (u : ∀ i, U i ⟶ S) (_ : ∀ i, Etale (u i)),
      (⋃ i, Set.range (u i) = .univ) ∧
        ∀ i, ∃ h : (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).obj
            (ModuleCat.of Λ (Fin a → Λ)) ⟶
            ((u i).smallEtalePullback (ModuleCat.{u} Λ)).obj E,
          h ≫ ((u i).smallEtalePullback (ModuleCat.{u} Λ)).map g ≫
            ((u i).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) N).hom =
            (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).map πN := by
  let F₀ : ModuleCat.{u} Λ := ModuleCat.of Λ (Fin a → Λ)
  let n : Fin a → N := fun k ↦ πN (Pi.single k 1)
  let T_S : S.Etale := Etale.mk (𝟙 S)
  let R := ⨅ k : Fin a, Presheaf.imageSieve g.hom
    ((toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj N)).app (op T_S) (n k))
  have hloc : Presheaf.IsLocallySurjective (smallEtaleTopology S) g.hom :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := g)).2 inferInstance
  have hR : R ∈ smallEtaleTopology S T_S :=
    (smallEtaleTopology S).iInf_mem fun k ↦ Presheaf.imageSieve_mem (smallEtaleTopology S) g.hom _
  obtain ⟨ι, U, u, hu_et, _, hαR, hcov⟩ := exists_etaleCover_of_mem_smallEtaleTopology_terminal hR
  refine ⟨ι, U, u, hu_et, hcov, fun i ↦ ?_⟩
  have := hu_et i
  obtain ⟨αi, hαi⟩ := hαR i
  choose s hs using fun k : Fin a ↦ (iInf_le _ k : R ≤ _) _ hαi
  let T_U : (U i).Etale := Etale.mk (𝟙 (U i))
  let hterm_U : IsTerminal T_U :=
    IsTerminal.isTerminalOfObj (Etale.forget (U i)) _ CategoryTheory.Over.mkIdTerminal
  let s' : Fin a → (((u i).smallEtalePullback (ModuleCat.{u} Λ)).obj E).obj.obj (op T_U) :=
    fun k ↦ (u i).evalUnitSelf E (s k)
  let h := ((constantSheafAdj (smallEtaleTopology (U i)) (ModuleCat.{u} Λ) hterm_U).homEquiv
    F₀ _).symm (ModuleCat.ofHom (Fintype.linearCombination Λ s'))
  refine ⟨h, ((constantSheafAdj (smallEtaleTopology (U i))
    (ModuleCat.{u} Λ) hterm_U).homEquiv F₀ _).injective ?_⟩
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply, constantSheafAdj_homEquiv_map]
  refine ModuleCat.hom_ext (LinearMap.ext fun c ↦ ?_)
  conv_lhs => rw [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.hom_ofHom, Fintype.linearCombination_apply, map_sum]
  conv_rhs => rw [pi_eq_sum_univ' c, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_smul, map_smul, map_smul]
  refine congrArg (c k • ·) ?_
  have hsk := (hs k).trans (toSheafify_app_const_map_apply (smallEtaleTopology S) N αi.op (n k))
  simpa only [Functor.flip_obj_map, ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, ConcreteCategory.comp_apply, s'] using
    (u i).smallEtalePullback_map_comp_constantSheafIso_evalUnitSelf g hsk

/-- Pushout step in the extension lemma: if `πN : F₀ ⟶ N` lifts to `h : const F₀ ⟶ E` and
`const (kernel.ι πN) ≫ h` factors through a linear map `gk : kernel πN ⟶ M` and `f : const M ⟶ E`,
then `E` is isomorphic to `const (pushout (kernel.ι πN) gk)` and hence finite lisse. -/
private theorem isFiniteLisse_of_shortExact_constantSheaf_of_lift_of_factor
    {S : Scheme.{u}} {M N F₀ : ModuleCat.{u} Λ}
    [Module.Finite Λ M] [Module.Finite Λ F₀]
    {E : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    {f : (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj M ⟶ E}
    {g : E ⟶ (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj N}
    {hfg : f ≫ g = 0} (hT : (ShortComplex.mk f g hfg).ShortExact)
    {πN : F₀ ⟶ N} [Epi πN]
    {h : (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj F₀ ⟶ E}
    (hhg : h ≫ g = (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).map πN)
    (gk : kernel πN ⟶ M)
    (hcomm : (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).map (kernel.ι πN) ≫ h =
      (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).map gk ≫ f) :
    E.IsFiniteLisse := by
  have : Module.Finite Λ N :=
    Module.Finite.of_surjective πN.hom ((ModuleCat.epi_iff_surjective πN).1 inferInstance)
  let sq := IsPushout.of_hasPushout (kernel.ι πN) gk
  let S_pres : ShortComplex (ModuleCat.{u} Λ) :=
    ShortComplex.mk (kernel.ι πN) πN (kernel.condition πN)
  have hS_pres : S_pres.ShortExact := TauCeti.kernelSequence_shortExact πN
  let T_mod : ShortComplex (ModuleCat.{u} Λ) :=
    ShortComplex.mk (pushout.inr (kernel.ι πN) gk) (TauCeti.cobaseChangeπ S_pres sq) (by simp)
  have hT_mod : T_mod.ShortExact := TauCeti.shortExact_cobaseChange hS_pres sq
  have hP_fin : Module.Finite Λ (Limits.pushout (C := ModuleCat.{u} Λ) (kernel.ι πN) gk) :=
    Module.Finite.of_exact ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T_mod).1
      hT_mod.exact) ((ModuleCat.epi_iff_surjective T_mod.g).1 hT_mod.epi_g)
  let sq_sheaf := (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).map_isPushout sq
  let Φ : (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj
      (pushout (kernel.ι πN) gk) ⟶ E :=
    sq_sheaf.desc h f hcomm
  have hΦ_r : Φ ≫ g =
      (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).map T_mod.g := by
    refine sq_sheaf.hom_ext ?_ ?_
    · rw [← Category.assoc, sq_sheaf.inl_desc, hhg, ← Functor.map_comp]
      exact congrArg ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).map)
        (TauCeti.inl_cobaseChangeπ S_pres sq).symm
    · rw [← Category.assoc, sq_sheaf.inr_desc, hfg, ← Functor.map_comp,
        TauCeti.inr_cobaseChangeπ S_pres sq, Functor.map_zero]
  let ψ_sc : T_mod.map (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)) ⟶
      ShortComplex.mk f g hfg :=
    { τ₁ := 𝟙 _
      τ₂ := Φ
      τ₃ := 𝟙 _
      comm₁₂ := by dsimp; rw [Category.id_comp]; exact (sq_sheaf.inr_desc h f hcomm).symm
      comm₂₃ := by dsimp; rw [Category.comp_id]; exact hΦ_r }
  have hIsoΦ : IsIso Φ :=
    ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ ψ_sc (shortExact_map_constantSheaf _ hT_mod) hT
  exact (isFiniteLisse_constantSheaf (pushout (kernel.ι πN) gk)).of_iso (asIso Φ)

/-- Splitting step in the extension lemma: given an epimorphism `πN : F₀ ⟶ N` (with `F₀` finitely
generated) lifting to `h : const F₀ ⟶ E`, pass to an étale cover trivializing the induced map
`const (kernel πN) ⟶ const M` and construct `E` locally as a pushout. -/
private theorem isFiniteLisse_of_shortExact_constantSheaf_of_lift [IsNoetherianRing Λ]
    {S : Scheme.{u}} {M N F₀ : ModuleCat.{u} Λ}
    [Module.Finite Λ M] [Module.Finite Λ F₀]
    {E : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    {f : (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj M ⟶ E}
    {g : E ⟶ (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj N}
    {hfg : f ≫ g = 0} (hT : (ShortComplex.mk f g hfg).ShortExact)
    {πN : F₀ ⟶ N} [Epi πN]
    {h : (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj F₀ ⟶ E}
    (hhg : h ≫ g = (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).map πN) :
    E.IsFiniteLisse := by
  have hKfin : Module.Finite Λ (Limits.kernel (C := ModuleCat.{u} Λ) πN) :=
    (ModuleCat.isFG_iff _).1 ((ModuleCat.isFG Λ).prop_of_mono (kernel.ι πN)
      ((ModuleCat.isFG_iff F₀).2 inferInstance))
  have hkh : ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).map (kernel.ι πN) ≫ h) ≫
      g = 0 := by
    rw [Category.assoc, hhg, ← Functor.map_comp, kernel.condition, Functor.map_zero]
  let ψ : (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj (kernel πN) ⟶
      (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj M :=
    (hT.fIsKernel.lift (Fork.ofι _ hkh) :)
  have hψf : ψ ≫ f =
      (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).map (kernel.ι πN) ≫ h :=
    hT.fIsKernel.fac (Fork.ofι _ hkh) WalkingParallelPair.zero
  obtain ⟨κ, V, v, _, hv_cov, hψ_loc⟩ := exists_etaleCover_map_constantSheaf (S := S) ψ
  rw [isFiniteLisse_iff_of_etaleCover E v hv_cov]
  intro j
  obtain ⟨gk, hgk⟩ := hψ_loc j
  let P := (v j).smallEtalePullback (ModuleCat.{u} Λ)
  let cF₀ := (v j).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) F₀
  let cM := (v j).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) M
  let cN := (v j).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) N
  have hh₂g₂ : (cF₀.inv ≫ P.map h) ≫ (P.map g ≫ cN.hom) =
      (constantSheaf (smallEtaleTopology (V j)) (ModuleCat.{u} Λ)).map πN := by
    dsimp only [cF₀, cN, P, Hom.smallEtalePullbackConstantSheafIso, Hom.smallEtalePullback]
    rw [Category.assoc,
      ← Category.assoc (((v j).smallEtaleBaseChange.sheafPullback _ _ _).map h),
      ← Functor.map_comp, hhg,
      ← Functor.sheafPullbackConstantSheafIso_inv_naturality_assoc, Iso.inv_hom_id,
      Category.comp_id]
  have hcomm :
      (constantSheaf (smallEtaleTopology (V j)) (ModuleCat.{u} Λ)).map (kernel.ι πN) ≫
        (cF₀.inv ≫ P.map h) =
      (constantSheaf (smallEtaleTopology (V j)) (ModuleCat.{u} Λ)).map gk ≫ (cM.inv ≫ P.map f) := by
    dsimp only [cF₀, cM, P, Hom.smallEtalePullbackConstantSheafIso, Hom.smallEtalePullback]
    rw [← Category.assoc, Functor.sheafPullbackConstantSheafIso_inv_naturality,
      Category.assoc, ← Functor.map_comp, ← hψf, Functor.map_comp, ← hgk]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact isFiniteLisse_of_shortExact_constantSheaf_of_lift_of_factor
    (shortExact_pullback_outerIso (v j) hT cM cN) hh₂g₂ gk hcomm

/-- Local extension lemma: the middle term of a short exact sequence whose outer terms are constant
sheaves on finitely generated modules over a left Noetherian ring `Λ` is finite lisse. -/
private theorem isFiniteLisse_of_shortExact_constantSheaf [IsNoetherianRing Λ]
    {S : Scheme.{u}} {M N : ModuleCat.{u} Λ} [Module.Finite Λ M] [Module.Finite Λ N]
    {E : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    {f : (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj M ⟶ E}
    {g : E ⟶ (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj N}
    {hfg : f ≫ g = 0} (hT : (ShortComplex.mk f g hfg).ShortExact) :
    E.IsFiniteLisse := by
  obtain ⟨a, πN_hom, hn⟩ := Module.Finite.exists_fin' Λ N
  let πN : ModuleCat.of Λ (Fin a → Λ) ⟶ N := ModuleCat.ofHom πN_hom
  have : Epi πN := (ModuleCat.epi_iff_surjective πN).2 hn
  have := hT.epi_g
  obtain ⟨ι, U, u, _, hcov, hlifts⟩ := exists_etaleCover_lift_constantSheaf_free g πN
  rw [isFiniteLisse_iff_of_etaleCover E u hcov]
  intro i
  obtain ⟨h, hh⟩ := hlifts i
  exact isFiniteLisse_of_shortExact_constantSheaf_of_lift
    (shortExact_pullback_outerIso (u i) hT
      ((u i).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) M)
      ((u i).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) N))
    hh

/-- Over a left Noetherian ring `Λ`, finite lisse étale sheaves of `Λ`-modules are closed under
extensions. -/
instance isClosedUnderExtensions_isFiniteLisse [IsNoetherianRing Λ] :
    ObjectProperty.IsClosedUnderExtensions
      (IsFiniteLisse : ObjectProperty (Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))) where
  prop_X₂_of_shortExact {T} hT h₁ h₃ := by
    obtain ⟨ι, U, u, hu_et, hu_cov, hpair⟩ := exists_etaleCover_pair_constantSheaf h₁ h₃
    rw [isFiniteLisse_iff_of_etaleCover T.X₂ u hu_cov]
    intro i
    obtain ⟨M, N, hM, hN, ⟨e₁⟩, ⟨e₃⟩⟩ := hpair i
    exact isFiniteLisse_of_shortExact_constantSheaf
      (shortExact_pullback_outerIso (u i) hT e₁ e₃)

end Closure

section DotNotation

variable {S : Scheme.{u}} {Λ : Type u} [Ring Λ]

/-- The middle term of a short exact sequence of étale sheaves of `Λ`-modules over a left
Noetherian ring `Λ` is finite lisse when both outer terms are finite lisse. -/
theorem IsFiniteLisse.of_shortExact [IsNoetherianRing Λ]
    {T : ShortComplex (Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))} (hT : T.ShortExact)
    (h₁ : T.X₁.IsFiniteLisse) (h₃ : T.X₃.IsFiniteLisse) : T.X₂.IsFiniteLisse :=
  ObjectProperty.prop_X₂_of_shortExact
    (P := (IsFiniteLisse : ObjectProperty (Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))))
    hT h₁ h₃

end DotNotation

end CategoryTheory.Sheaf
