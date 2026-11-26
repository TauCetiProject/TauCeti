/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.AlgebraicGeometry.Sites.Etale.ModuleSheaf
public import TauCeti.CategoryTheory.Exact.Abelian
public import TauCeti.CategoryTheory.Sites.Limits

/-!
# Finite lisse étale sheaves form a weak Serre class

Let `S` be a scheme and `Λ` a ring. This file proves that finite lisse étale sheaves of
`Λ`-modules on `S` (`CategoryTheory.Sheaf.IsFiniteLisse`) are closed under cokernels over any ring
`Λ`, and closed under kernels and extensions when `Λ` is left Noetherian: together with
`CategoryTheory.Sheaf.containsZero_isFiniteLisse` and closure under isomorphisms, they form a weak
Serre class in `Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)`.

The core local step is that any morphism `(constantSheaf _ _).obj M ⟶ (constantSheaf _ _).obj N`
out of a constant sheaf with finitely generated `Λ`-module value `M` comes étale-locally from a
constant `Λ`-linear map `M ⟶ N` (`CategoryTheory.Sheaf.exists_etaleCover_map_constantSheaf`):
evaluating the sheaf morphism on a finite generating set of `M` produces finitely many global
sections of `(constantSheaf _ _).obj N`, which become constant on a common étale covering sieve.
Exactness of `constantSheaf` then shows that its kernel and cokernel are locally constant, with
finitely generated values once `Λ` is left Noetherian (for cokernels, over any ring).

For an extension `0 ⟶ F ⟶ E ⟶ G ⟶ 0` with `F` and `G` finite lisse over left Noetherian `Λ`,
pass to a common trivializing étale cover so `F` and `G` are constant on finitely generated modules
`M` and `N`. Choose a finite presentation `0 ⟶ K ⟶ Λ^a ⟶ N ⟶ 0` (whose kernel `K` is finitely
generated since `Λ` is left Noetherian); lift the basis of `Λ^a` étale-locally to `E`, factor the
induced map on `const K` locally through a linear map `g : K ⟶ M`, and push out `K ⟶ Λ^a` along
`g` to obtain a finitely generated module `P` whose constant sheaf maps isomorphically to `E` by
the short five lemma.

## Main results

* `CategoryTheory.Sheaf.exists_etaleCover_map_constantSheaf`: a morphism between constant étale
  sheaves on `Λ`-modules whose source is finitely generated is étale-locally constant.
* `CategoryTheory.Sheaf.isClosedUnderCokernels_isFiniteLisse`: finite lisse sheaves are closed under
  cokernels over any ring `Λ`.
* `CategoryTheory.Sheaf.isClosedUnderKernels_isFiniteLisse`: finite lisse sheaves are closed under
  kernels over any left Noetherian ring `Λ`.
* `CategoryTheory.Sheaf.isClosedUnderExtensions_isFiniteLisse`: finite lisse sheaves are closed
  under extensions over any left Noetherian ring `Λ`.
* `CategoryTheory.Sheaf.IsFiniteLisse.cokernel`, `CategoryTheory.Sheaf.IsFiniteLisse.kernel`,
  `CategoryTheory.Sheaf.IsFiniteLisse.of_shortExact`: dot-notation forms.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IX, §2.7.
* The Stacks Project, Section 59.64 and Section 59.71, Tag 03RZ.
-/

public section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry Scheme

namespace CategoryTheory.Sheaf

section Exactness

variable {S : Scheme.{u}} (Λ : Type u) [Ring Λ]

/-- The constant sheaf functor on the small étale site of `S` with values in `Λ`-modules preserves
finite colimits. -/
instance preservesFiniteColimits_constantSheaf_smallEtaleTopology :
    PreservesFiniteColimits (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)) :=
  comp_preservesFiniteColimits _ _

/-- The constant sheaf functor on the small étale site of `S` with values in `Λ`-modules preserves
short exact sequences. -/
theorem shortExact_map_constantSheaf_smallEtaleTopology
    {T : ShortComplex (ModuleCat.{u} Λ)} (hT : T.ShortExact) :
    (T.map (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))).ShortExact :=
  hT.map_of_exact _

/-- Inverse image of étale sheaves of `Λ`-modules preserves finite colimits, being a left
adjoint. -/
instance preservesFiniteColimits_smallEtalePullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (f.smallEtalePullback (ModuleCat.{u} Λ)) :=
  ⟨fun _ _ _ ↦ ((f.smallEtaleAdjunction
    (ModuleCat.{u} Λ)).leftAdjoint_preservesColimits.{0, 0}).preservesColimitsOfShape⟩

end Exactness

section ConstantSheafLocal

variable {S : Scheme.{u}} {Λ : Type u} [Ring Λ]

/-- On a nonempty étale `S`-scheme `U`, the canonical map from `M` into the sections over `U` of
the constant étale sheaf on `M` is injective: two elements agreeing there agree on a covering
sieve, which must contain an étale scheme over `U`. -/
private theorem injective_toSheafify_app_const_smallEtaleTopology
    (M : ModuleCat.{u} Λ) {U : S.Etale} (hU : Nonempty U.left) :
    Function.Injective
      ((toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj M)).app (op U)) := by
  intro m₁ m₂ hm
  have hmem : Presheaf.equalizerSieve (F := (Functor.const S.Etaleᵒᵖ).obj M) (X := op U) m₁ m₂ ∈
      smallEtaleTopology S U :=
    Presheaf.equalizerSieve_mem (smallEtaleTopology S) _ m₁ m₂ hm
  obtain ⟨ι, V, g, hR⟩ := (Presheaf.equalizerSieve (F := (Functor.const S.Etaleᵒᵖ).obj M)
    (X := op U) m₁ m₂).exists_eq_ofArrows
  have hcov := (ofArrows_mem_smallEtaleTopology_iff g).mp (hR ▸ hmem)
  obtain ⟨x⟩ := hU
  have hx : x ∈ ⋃ i, Set.range (g i).left := by
    rw [hcov]
    trivial
  obtain ⟨i, _, -⟩ := Set.mem_iUnion.mp hx
  have hg : Presheaf.equalizerSieve (F := (Functor.const S.Etaleᵒᵖ).obj M) (X := op U)
      m₁ m₂ (g i) :=
    hR.symm ▸ Sieve.ofArrows_mk V g i
  simpa using hg

/-- Intersection of a finite family of covering sieves in a Grothendieck topology indexed by
`Fin n` is a covering sieve. -/
private theorem iInf_fin_mem_grothendieckTopology {C : Type*} [Category* C]
    (J : GrothendieckTopology C) {X : C} {n : ℕ} (R : Fin n → Sieve X)
    (hR : ∀ i, R i ∈ J X) : (⨅ i, R i) ∈ J X := by
  induction n with
  | zero =>
    convert J.top_mem X
    exact top_unique fun Y f _ ↦ by simp
  | succ n ih =>
    have hsplit : (⨅ i : Fin (n + 1), R i) = R 0 ⊓ ⨅ i : Fin n, R i.succ := by
      refine le_antisymm (le_inf (iInf_le R 0) (le_iInf fun i ↦ iInf_le R i.succ)) ?_
      refine le_iInf fun i ↦ Fin.cases inf_le_left (fun j ↦ inf_le_right.trans (iInf_le _ j)) i
    rw [hsplit]
    exact J.intersection_covering (hR 0) (ih (fun i ↦ R i.succ) fun i ↦ hR i.succ)

/-- A covering sieve on the terminal étale `S`-scheme `Etale.mk (𝟙 S)` yields a `Type u`-indexed
jointly surjective family of nonempty étale `S`-schemes whose morphisms to `Etale.mk (𝟙 S)` lie in
the sieve. -/
private theorem exists_etaleCover_of_mem_smallEtaleTopology_terminal
    {R : Sieve (Etale.mk (𝟙 S))} (hR : R ∈ smallEtaleTopology S (Etale.mk (𝟙 S))) :
    ∃ (ι : Type u) (U : ι → Scheme.{u}) (u : ∀ i, U i ⟶ S) (hu : ∀ i, Etale (u i)),
      (∀ i, Nonempty (U i)) ∧
        (∀ i, ∃ g : @Etale.mk S (U i) (u i) (hu i) ⟶ Etale.mk (𝟙 S), R g) ∧
        (⋃ i, Set.range (u i) = .univ) := by
  obtain ⟨ι', V, g', heq⟩ := R.exists_eq_ofArrows
  have hcov := (ofArrows_mem_smallEtaleTopology_iff g').mp (heq ▸ hR)
  have hg' (j : ι') : ((g' j).left : (V j).left ⟶ S) = (V j).hom :=
    (Category.comp_id _).symm.trans (CategoryTheory.Over.w ((Etale.forget S).map (g' j)))
  choose idx hidx using fun s : S ↦ Set.mem_iUnion.mp (hcov ▸ Set.mem_univ s)
  refine ⟨S, fun s ↦ (V (idx s)).left, fun s ↦ (V (idx s)).hom, fun s ↦ (V (idx s)).prop,
    fun s ↦ ?_, fun s ↦ ?_, Set.eq_univ_of_forall fun s ↦ ?_⟩
  · obtain ⟨z, -⟩ := hidx s
    exact ⟨z⟩
  · exact ⟨g' (idx s), heq.symm ▸ Sieve.ofArrows_mk V g' (idx s)⟩
  · obtain ⟨z, hz⟩ := hidx s
    exact Set.mem_iUnion.mpr ⟨s, z, (congrArg (fun f : (V (idx s)).left ⟶ S ↦ f z)
      (hg' (idx s)).symm).trans hz⟩

/-- For an étale morphism `u : U ⟶ S`, the diagonal
`Etale.mk (𝟙 U) ⟶ u.smallEtaleBaseChange.obj (Etale.mk u)`. -/
private noncomputable def smallEtaleBaseChangeSelfDiag {U : Scheme.{u}} (u : U ⟶ S) [Etale u] :
    Etale.mk (𝟙 U) ⟶ u.smallEtaleBaseChange.obj (Etale.mk u) :=
  MorphismProperty.Over.homMk (pullback.lift (𝟙 U) (𝟙 U) rfl) (pullback.lift_snd _ _ _)

/-- Pulling a section of `F` over `Etale.mk u` back to the terminal object `Etale.mk (𝟙 U)` of
`U.Etale` along the adjunction unit and the diagonal `smallEtaleBaseChangeSelfDiag u`. -/
private noncomputable def evalUnitSelf {U : Scheme.{u}} (u : U ⟶ S) [Etale u]
    (F : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)) :
    F.obj.obj (op (Etale.mk u)) ⟶
      ((u.smallEtalePullback (ModuleCat.{u} Λ)).obj F).obj.obj (op (Etale.mk (𝟙 U))) :=
  ((u.smallEtaleAdjunction (ModuleCat.{u} Λ)).unit.app F).hom.app (op (Etale.mk u)) ≫
    ((u.smallEtalePullback (ModuleCat.{u} Λ)).obj F).obj.map
      (smallEtaleBaseChangeSelfDiag u).op

private lemma evalUnitSelf_naturality {U : Scheme.{u}} (u : U ⟶ S) [Etale u]
    {F G : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)} (φ : F ⟶ G) :
    φ.hom.app (op (Etale.mk u)) ≫ evalUnitSelf u G =
      evalUnitSelf u F ≫ ((u.smallEtalePullback (ModuleCat.{u} Λ)).map φ).hom.app
        (op (Etale.mk (𝟙 U))) := by
  have h₁ := NatTrans.congr_app
    (congrArg (·.hom) ((u.smallEtaleAdjunction (ModuleCat.{u} Λ)).unit.naturality φ))
    (op (Etale.mk u))
  have h₂ := ((u.smallEtalePullback (ModuleCat.{u} Λ)).map φ).hom.naturality
    (smallEtaleBaseChangeSelfDiag u).op
  calc
    φ.hom.app (op (Etale.mk u)) ≫ evalUnitSelf u G
      = (φ.hom.app (op (Etale.mk u)) ≫
          ((u.smallEtaleAdjunction (ModuleCat.{u} Λ)).unit.app G).hom.app (op (Etale.mk u))) ≫
          ((u.smallEtalePullback (ModuleCat.{u} Λ)).obj G).obj.map
            (smallEtaleBaseChangeSelfDiag u).op := (Category.assoc _ _ _).symm
    _ = (((u.smallEtaleAdjunction (ModuleCat.{u} Λ)).unit.app F).hom.app (op (Etale.mk u)) ≫
          ((u.smallEtalePullback (ModuleCat.{u} Λ)).map φ).hom.app
            (op (u.smallEtaleBaseChange.obj (Etale.mk u)))) ≫
          ((u.smallEtalePullback (ModuleCat.{u} Λ)).obj G).obj.map
            (smallEtaleBaseChangeSelfDiag u).op := eq_whisker h₁ _
    _ = ((u.smallEtaleAdjunction (ModuleCat.{u} Λ)).unit.app F).hom.app (op (Etale.mk u)) ≫
          (((u.smallEtalePullback (ModuleCat.{u} Λ)).map φ).hom.app
            (op (u.smallEtaleBaseChange.obj (Etale.mk u))) ≫
          ((u.smallEtalePullback (ModuleCat.{u} Λ)).obj G).obj.map
            (smallEtaleBaseChangeSelfDiag u).op) := Category.assoc _ _ _
    _ = ((u.smallEtaleAdjunction (ModuleCat.{u} Λ)).unit.app F).hom.app (op (Etale.mk u)) ≫
          (((u.smallEtalePullback (ModuleCat.{u} Λ)).obj F).obj.map
            (smallEtaleBaseChangeSelfDiag u).op ≫
          ((u.smallEtalePullback (ModuleCat.{u} Λ)).map φ).hom.app (op (Etale.mk (𝟙 U)))) :=
        whisker_eq _ h₂.symm
    _ = evalUnitSelf u F ≫ ((u.smallEtalePullback (ModuleCat.{u} Λ)).map φ).hom.app
          (op (Etale.mk (𝟙 U))) := (Category.assoc _ _ _).symm

private lemma toSheafify_comp_evalUnitSelf {U : Scheme.{u}} (u : U ⟶ S) [Etale u]
    (M : ModuleCat.{u} Λ) :
    (toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj M)).app (op (Etale.mk u)) ≫
        evalUnitSelf u ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj M) =
      (toSheafify (smallEtaleTopology U) ((Functor.const U.Etaleᵒᵖ).obj M)).app
          (op (Etale.mk (𝟙 U))) ≫
        (u.smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) M).inv.hom.app
          (op (Etale.mk (𝟙 U))) := by
  have hw := NatTrans.congr_app
    (u.smallEtaleBaseChange.whiskerLeft_toSheafify_comp_sheafPullbackConstantSheafIso_inv
      (ModuleCat.{u} Λ) (smallEtaleTopology S) (smallEtaleTopology U) M) (op (Etale.mk u))
  have hnat := ((u.smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) M).inv.hom.naturality
    (smallEtaleBaseChangeSelfDiag u).op).symm
  have hrest := toSheafify_app_const_comp_map (smallEtaleTopology U) M
    (smallEtaleBaseChangeSelfDiag u).op
  calc
    (toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj M)).app (op (Etale.mk u)) ≫
        evalUnitSelf u ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj M)
      = ((toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj M)).app
          (op (Etale.mk u)) ≫
          ((u.smallEtaleAdjunction (ModuleCat.{u} Λ)).unit.app
            ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj M)).hom.app
            (op (Etale.mk u))) ≫
          ((u.smallEtalePullback (ModuleCat.{u} Λ)).obj
            ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj M)).obj.map
            (smallEtaleBaseChangeSelfDiag u).op := (Category.assoc _ _ _).symm
    _ = ((toSheafify (smallEtaleTopology U) ((Functor.const U.Etaleᵒᵖ).obj M)).app
          (op (u.smallEtaleBaseChange.obj (Etale.mk u))) ≫
          (u.smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) M).inv.hom.app
            (op (u.smallEtaleBaseChange.obj (Etale.mk u)))) ≫
          ((u.smallEtalePullback (ModuleCat.{u} Λ)).obj
            ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj M)).obj.map
            (smallEtaleBaseChangeSelfDiag u).op := eq_whisker hw.symm _
    _ = (toSheafify (smallEtaleTopology U) ((Functor.const U.Etaleᵒᵖ).obj M)).app
          (op (u.smallEtaleBaseChange.obj (Etale.mk u))) ≫
          ((u.smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) M).inv.hom.app
            (op (u.smallEtaleBaseChange.obj (Etale.mk u))) ≫
          ((u.smallEtalePullback (ModuleCat.{u} Λ)).obj
            ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj M)).obj.map
            (smallEtaleBaseChangeSelfDiag u).op) := Category.assoc _ _ _
    _ = (toSheafify (smallEtaleTopology U) ((Functor.const U.Etaleᵒᵖ).obj M)).app
          (op (u.smallEtaleBaseChange.obj (Etale.mk u))) ≫
          (((constantSheaf (smallEtaleTopology U) (ModuleCat.{u} Λ)).obj M).obj.map
            (smallEtaleBaseChangeSelfDiag u).op ≫
          (u.smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) M).inv.hom.app
            (op (Etale.mk (𝟙 U)))) := whisker_eq _ hnat
    _ = ((toSheafify (smallEtaleTopology U) ((Functor.const U.Etaleᵒᵖ).obj M)).app
          (op (u.smallEtaleBaseChange.obj (Etale.mk u))) ≫
          ((constantSheaf (smallEtaleTopology U) (ModuleCat.{u} Λ)).obj M).obj.map
            (smallEtaleBaseChangeSelfDiag u).op) ≫
          (u.smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) M).inv.hom.app
            (op (Etale.mk (𝟙 U))) := (Category.assoc _ _ _).symm
    _ = (toSheafify (smallEtaleTopology U) ((Functor.const U.Etaleᵒᵖ).obj M)).app
          (op (Etale.mk (𝟙 U))) ≫
          (u.smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) M).inv.hom.app
            (op (Etale.mk (𝟙 U))) := eq_whisker hrest _

/-- **Local constancy of morphisms between constant sheaves.** Let `φ : const M ⟶ const N` be a
morphism of constant étale sheaves of `Λ`-modules on `S`, with `M` finitely generated. Then there
exists a `Type u`-indexed jointly surjective étale cover `u : ∀ i, U i ⟶ S` such that over each
`U i`, the pullback of `φ` identifies (under `smallEtalePullbackConstantSheafIso`) with the constant
sheaf on a `Λ`-linear map `f i : M ⟶ N`. -/
theorem exists_etaleCover_map_constantSheaf {M N : ModuleCat.{u} Λ} [Module.Finite Λ M]
    (φ : (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj M ⟶
      (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj N) :
    ∃ (ι : Type u) (U : ι → Scheme.{u}) (u : ∀ i, U i ⟶ S) (_ : ∀ i, Etale (u i)),
      (⋃ i, Set.range (u i) = .univ) ∧
        ∀ i, ∃ f : M ⟶ N,
          ((u i).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) M).inv ≫
            ((u i).smallEtalePullback (ModuleCat.{u} Λ)).map φ ≫
            ((u i).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) N).hom =
              (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).map f := by
  obtain ⟨r, p_hom, hm⟩ := Module.Finite.exists_fin' Λ M
  let m : Fin r → M := fun k ↦ p_hom (Pi.single k 1)
  let T_S : S.Etale := Etale.mk (𝟙 S)
  let hterm_S : IsTerminal T_S :=
    IsTerminal.isTerminalOfObj (Etale.forget S) _ CategoryTheory.Over.mkIdTerminal
  let σ : M →ₗ[Λ] ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj N).obj.obj
      (op T_S) :=
    (((constantSheafAdj (smallEtaleTopology S) (ModuleCat.{u} Λ) hterm_S).homEquiv M _ φ)).hom
  have hσ (a : M) : σ a = φ.hom.app (op T_S)
      ((toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj M)).app (op T_S) a) := by
    simp [σ, constantSheafAdj, Adjunction.homEquiv_apply, Adjunction.comp_unit_app,
      sheafificationAdjunction_unit_app, constantPresheafAdj_unit_app]
  let R := ⨅ k : Fin r, Presheaf.imageSieve
    (toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj N)) (σ (m k))
  have hR : R ∈ smallEtaleTopology S T_S :=
    iInf_fin_mem_grothendieckTopology (smallEtaleTopology S) _ fun k ↦
      Presheaf.imageSieve_mem (smallEtaleTopology S) _ (σ (m k))
  obtain ⟨ι, U, u, hu_et, hUne, hgR, hcov⟩ :=
    exists_etaleCover_of_mem_smallEtaleTopology_terminal hR
  refine ⟨ι, U, u, hu_et, hcov, fun i ↦ ?_⟩
  have := hu_et i
  obtain ⟨gi, hgi⟩ := hgR i
  have hg_mem (k : Fin r) : Presheaf.imageSieve
      (toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj N)) (σ (m k)) gi := by
    have hle : R ≤ _ := iInf_le _ k
    exact hle _ hgi
  choose n hn using fun k : Fin r ↦ hg_mem k
  let p : (Fin r → Λ) →ₗ[Λ] M := Fintype.linearCombination Λ m
  let q : (Fin r → Λ) →ₗ[Λ] N := Fintype.linearCombination Λ n
  have hp_eq (c : Fin r → Λ) : p c = p_hom c := by
    have hc : c = ∑ k : Fin r, c k • Pi.single k (1 : Λ) := by
      ext j
      simp [Pi.single_apply]
    conv_rhs => rw [hc]
    simp [p, m, map_sum, map_smul, Fintype.linearCombination_apply]
  have hm' : Function.Surjective p := by
    intro y
    obtain ⟨c, rfl⟩ := hm y
    exact ⟨c, hp_eq c⟩
  have hker : LinearMap.ker p ≤ LinearMap.ker q := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    apply injective_toSheafify_app_const_smallEtaleTopology N (U := Etale.mk (u i)) (hUne i)
    have heq : (toSheafify (smallEtaleTopology S)
          ((Functor.const S.Etaleᵒᵖ).obj N)).app (op (Etale.mk (u i))) (q c) =
        ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj N).obj.map gi.op
          (σ (p c)) := by
      simp only [q, p, Fintype.linearCombination_apply, map_sum, map_smul]
      refine Finset.sum_congr rfl fun k _ ↦ congrArg (c k • ·) ?_
      exact hn k
    rw [hc, map_zero, map_zero] at heq
    exact heq.trans (map_zero _).symm
  let f : M →ₗ[Λ] N :=
    ((LinearMap.ker p).liftQ q hker).comp (p.quotKerEquivOfSurjective hm').symm.toLinearMap
  have hf_eq (c : Fin r → Λ) : f (p c) = q c := by
    have hq : (p.quotKerEquivOfSurjective hm').symm (p c) = Submodule.Quotient.mk c :=
      (p.quotKerEquivOfSurjective hm').symm_apply_eq.mpr rfl
    change ((LinearMap.ker p).liftQ q hker) ((p.quotKerEquivOfSurjective hm').symm (p c)) = q c
    rw [hq, Submodule.liftQ_apply]
  refine ⟨ModuleCat.ofHom f, ?_⟩
  let T_U : (U i).Etale := Etale.mk (𝟙 (U i))
  let hterm_U : IsTerminal T_U :=
    IsTerminal.isTerminalOfObj (Etale.forget (U i)) _ CategoryTheory.Over.mkIdTerminal
  apply ((constantSheafAdj (smallEtaleTopology (U i))
    (ModuleCat.{u} Λ) hterm_U).homEquiv M _).injective
  ext x
  obtain ⟨c, rfl⟩ := hm' x
  have hφc : φ.hom.app (op (Etale.mk (u i)))
      ((toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj M)).app
        (op (Etale.mk (u i))) (p c)) =
      (toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj N)).app
        (op (Etale.mk (u i))) (f (p c)) := by
    rw [hf_eq c]
    have hnat : φ.hom.app (op (Etale.mk (u i)))
        (((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj M).obj.map gi.op
          ((toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj M)).app
            (op T_S) (p c))) =
        ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj N).obj.map gi.op
          (φ.hom.app (op T_S)
            ((toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj M)).app
              (op T_S) (p c))) := by
      rw [← ConcreteCategory.comp_apply, φ.hom.naturality gi.op, ConcreteCategory.comp_apply]
    rw [toSheafify_app_const_map_apply] at hnat
    rw [hnat, ← hσ]
    simp only [p, q, Fintype.linearCombination_apply, map_sum, map_smul]
    refine Finset.sum_congr rfl fun k _ ↦ congrArg (c k • ·) ?_
    exact (hn k).symm
  -- Transport `hφc` along `evalUnitSelf` to `Etale.mk (𝟙 (U i))`.
  have heval := congrArg (evalUnitSelf (u i)
    ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj N)) hφc
  have hlhs : evalUnitSelf (u i)
      ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj N)
      (φ.hom.app (op (Etale.mk (u i))) ((toSheafify (smallEtaleTopology S)
        ((Functor.const S.Etaleᵒᵖ).obj M)).app (op (Etale.mk (u i))) (p c))) =
      ((((u i).smallEtalePullback (ModuleCat.{u} Λ)).map φ).hom.app (op T_U)
        (((u i).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) M).inv.hom.app (op T_U)
          ((toSheafify (smallEtaleTopology (U i)) ((Functor.const (U i).Etaleᵒᵖ).obj M)).app
            (op T_U) (p c)))) := by
    rw [← ConcreteCategory.comp_apply, evalUnitSelf_naturality (u i) φ,
      ConcreteCategory.comp_apply]
    exact congrArg ((((u i).smallEtalePullback (ModuleCat.{u} Λ)).map φ).hom.app (op T_U))
      (ConcreteCategory.congr_hom (toSheafify_comp_evalUnitSelf (u i) M) (p c))
  have hrhs : evalUnitSelf (u i)
      ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj N)
      ((toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj N)).app
        (op (Etale.mk (u i))) (f (p c))) =
      ((u i).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) N).inv.hom.app (op T_U)
        ((toSheafify (smallEtaleTopology (U i)) ((Functor.const (U i).Etaleᵒᵖ).obj N)).app
          (op T_U) (f (p c))) :=
    ConcreteCategory.congr_hom (toSheafify_comp_evalUnitSelf (u i) N) (f (p c))
  rw [hlhs, hrhs] at heval
  have heval' := congrArg
    (((u i).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) N).hom.hom.app (op T_U)) heval
  have hinv_hom :
      ((u i).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) N).inv.hom.app (op T_U) ≫
        ((u i).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) N).hom.hom.app (op T_U) =
        𝟙 _ := by
    rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id]
    rfl
  have heval'' :
      ((u i).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) N).hom.hom.app (op T_U)
        ((((u i).smallEtalePullback (ModuleCat.{u} Λ)).map φ).hom.app (op T_U)
          (((u i).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) M).inv.hom.app (op T_U)
            ((toSheafify (smallEtaleTopology (U i))
              ((Functor.const (U i).Etaleᵒᵖ).obj M)).app (op T_U) (p c)))) =
        (toSheafify (smallEtaleTopology (U i)) ((Functor.const (U i).Etaleᵒᵖ).obj N)).app
          (op T_U) (f (p c)) := by
    refine heval'.trans ?_
    rw [← ConcreteCategory.comp_apply, hinv_hom, ConcreteCategory.id_apply]
  unfold constantSheaf
  simp only [constantSheafAdj, Adjunction.comp_homEquiv, Equiv.trans_apply,
    Adjunction.homEquiv_unit, constantPresheafAdj_unit_app, Category.id_comp,
    sheafificationAdjunction_unit_app, Functor.comp_obj, Functor.comp_map]
  change ((u i).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) N).hom.hom.app (op T_U)
      ((((u i).smallEtalePullback (ModuleCat.{u} Λ)).map φ).hom.app (op T_U)
        (((u i).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) M).inv.hom.app (op T_U)
          ((toSheafify (smallEtaleTopology (U i))
            ((Functor.const (U i).Etaleᵒᵖ).obj M)).app (op T_U) (p c)))) =
    (sheafifyMap (smallEtaleTopology (U i))
      ((Functor.const (U i).Etaleᵒᵖ).map (ModuleCat.ofHom f))).app (op T_U)
      ((toSheafify (smallEtaleTopology (U i))
        ((Functor.const (U i).Etaleᵒᵖ).obj M)).app (op T_U) (p c))
  rw [heval'', ← ConcreteCategory.comp_apply, ← NatTrans.comp_app]
  have hnat := NatTrans.congr_app
    (toSheafify_naturality (smallEtaleTopology (U i))
      ((Functor.const (U i).Etaleᵒᵖ).map (ModuleCat.ofHom f))) (op T_U)
  exact ConcreteCategory.congr_hom hnat (p c)

end ConstantSheafLocal

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
    Set.eq_univ_of_forall fun s ↦ ?_, fun p ↦ ?_⟩
  · obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.mp (hu_cov ▸ Set.mem_univ s)
    obtain ⟨k, z, rfl⟩ := Set.mem_iUnion.mp (hv_cov i ▸ Set.mem_univ x)
    exact Set.mem_iUnion.mpr ⟨⟨i, k⟩, z, Scheme.Hom.comp_apply (v i k) (u i) z⟩
  · obtain ⟨M, hM, ⟨eF⟩⟩ := htrivF p.1
    obtain ⟨N, hN, ⟨eG⟩⟩ := htrivG p.1 p.2
    have hcompF := (Hom.smallEtalePullbackComp (v p.1 p.2) (u p.1) (ModuleCat.{u} Λ)).app F
    have hcompG := (Hom.smallEtalePullbackComp (v p.1 p.2) (u p.1) (ModuleCat.{u} Λ)).app G
    refine ⟨M, N, hM, hN,
      ⟨hcompF ≪≫ ((v p.1 p.2).smallEtalePullback (ModuleCat.{u} Λ)).mapIso eF ≪≫
        (v p.1 p.2).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) M⟩,
      ⟨hcompG ≪≫ eG⟩⟩

/-- Given a morphism `φ : F ⟶ G` between finite lisse sheaves on `S`, there exists a
`Type u`-indexed jointly surjective étale cover of `S` over each piece of which `F` and `G` are
isomorphic to constant sheaves on finitely generated `Λ`-modules and `φ` identifies with a
constant linear map. -/
private theorem exists_etaleCover_hom_constantSheaf
    {F G : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    (hF : F.IsFiniteLisse) (hG : G.IsFiniteLisse) (φ : F ⟶ G) :
    ∃ (ι : Type u) (U : ι → Scheme.{u}) (u : ∀ i, U i ⟶ S) (_ : ∀ i, Etale (u i)),
      (⋃ i, Set.range (u i) = .univ) ∧
        ∀ i, ∃ (M N : ModuleCat.{u} Λ) (_ : Module.Finite Λ M) (_ : Module.Finite Λ N)
          (eF : ((u i).smallEtalePullback (ModuleCat.{u} Λ)).obj F ≅
            (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).obj M)
          (eG : ((u i).smallEtalePullback (ModuleCat.{u} Λ)).obj G ≅
            (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).obj N)
          (f : M ⟶ N),
          eF.inv ≫ ((u i).smallEtalePullback (ModuleCat.{u} Λ)).map φ ≫ eG.hom =
            (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).map f := by
  obtain ⟨ι, U, u, hu_et, hu_cov, hpair⟩ := exists_etaleCover_pair_constantSheaf hF hG
  choose M N hM hN heF heG using hpair
  let eF (i : ι) := (heF i).some
  let eG (i : ι) := (heG i).some
  choose κ V v hv_et hv_cov hf using fun i ↦
    exists_etaleCover_map_constantSheaf (S := U i) (Λ := Λ)
      ((eF i).inv ≫ ((u i).smallEtalePullback (ModuleCat.{u} Λ)).map φ ≫ (eG i).hom)
  refine ⟨Σ i, κ i, fun p ↦ V p.1 p.2, fun p ↦ v p.1 p.2 ≫ u p.1,
    fun p ↦ have := hu_et p.1; have := hv_et p.1 p.2; inferInstance,
    Set.eq_univ_of_forall fun s ↦ ?_, fun p ↦ ?_⟩
  · obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.mp (hu_cov ▸ Set.mem_univ s)
    obtain ⟨k, z, rfl⟩ := Set.mem_iUnion.mp (hv_cov i ▸ Set.mem_univ x)
    exact Set.mem_iUnion.mpr ⟨⟨i, k⟩, z, Scheme.Hom.comp_apply (v i k) (u i) z⟩
  · obtain ⟨f, hfk⟩ := hf p.1 p.2
    let pF := (Hom.smallEtalePullbackComp (v p.1 p.2) (u p.1) (ModuleCat.{u} Λ)).app F
    let pG := (Hom.smallEtalePullbackComp (v p.1 p.2) (u p.1) (ModuleCat.{u} Λ)).app G
    let cF := (v p.1 p.2).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) (M p.1)
    let cG := (v p.1 p.2).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) (N p.1)
    let eF' : ((v p.1 p.2 ≫ u p.1).smallEtalePullback (ModuleCat.{u} Λ)).obj F ≅
        (constantSheaf (smallEtaleTopology (V p.1 p.2)) (ModuleCat.{u} Λ)).obj (M p.1) :=
      pF ≪≫ ((v p.1 p.2).smallEtalePullback (ModuleCat.{u} Λ)).mapIso (eF p.1) ≪≫ cF
    let eG' : ((v p.1 p.2 ≫ u p.1).smallEtalePullback (ModuleCat.{u} Λ)).obj G ≅
        (constantSheaf (smallEtaleTopology (V p.1 p.2)) (ModuleCat.{u} Λ)).obj (N p.1) :=
      pG ≪≫ ((v p.1 p.2).smallEtalePullback (ModuleCat.{u} Λ)).mapIso (eG p.1) ≪≫ cG
    refine ⟨M p.1, N p.1, hM p.1, hN p.1, eF', eG', f, ?_⟩
    have hnat := (Hom.smallEtalePullbackComp (v p.1 p.2) (u p.1) (ModuleCat.{u} Λ)).hom.naturality φ
    dsimp at hnat
    have hnat' : pF.inv ≫ ((v p.1 p.2 ≫ u p.1).smallEtalePullback (ModuleCat.{u} Λ)).map φ ≫
        pG.hom = ((v p.1 p.2).smallEtalePullback (ModuleCat.{u} Λ)).map
          (((u p.1).smallEtalePullback (ModuleCat.{u} Λ)).map φ) := by
      rw [Iso.inv_comp_eq]
      exact hnat
    calc
      eF'.inv ≫ ((v p.1 p.2 ≫ u p.1).smallEtalePullback (ModuleCat.{u} Λ)).map φ ≫ eG'.hom
        = cF.inv ≫ ((v p.1 p.2).smallEtalePullback (ModuleCat.{u} Λ)).map (eF p.1).inv ≫
            (pF.inv ≫ ((v p.1 p.2 ≫ u p.1).smallEtalePullback (ModuleCat.{u} Λ)).map φ ≫
              pG.hom) ≫
            ((v p.1 p.2).smallEtalePullback (ModuleCat.{u} Λ)).map (eG p.1).hom ≫ cG.hom := by
          simp only [eF', eG', Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
            Category.assoc]
      _ = cF.inv ≫ ((v p.1 p.2).smallEtalePullback (ModuleCat.{u} Λ)).map
            ((eF p.1).inv ≫ ((u p.1).smallEtalePullback (ModuleCat.{u} Λ)).map φ ≫
              (eG p.1).hom) ≫ cG.hom := by
          rw [hnat']
          simp only [Functor.map_comp, Category.assoc]
      _ = (constantSheaf (smallEtaleTopology (V p.1 p.2)) (ModuleCat.{u} Λ)).map f := hfk

/-- Over any ring `Λ`, finite lisse étale sheaves of `Λ`-modules are closed under cokernels. -/
instance isClosedUnderCokernels_isFiniteLisse :
    ObjectProperty.IsClosedUnderCokernels
      (IsFiniteLisse : ObjectProperty (Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))) where
  cokernels_le := by
    rintro _ ⟨φ, k, hk, hF, hG⟩
    obtain ⟨ι, U, u, hu_et, hu_cov, hφ⟩ := exists_etaleCover_hom_constantSheaf hF hG φ
    refine IsFiniteLisse.of_etaleCover_constantSheaf u hu_cov fun i ↦ ?_
    obtain ⟨M, N, _, _, eF, eG, f, hf⟩ := hφ i
    have hfin : Module.Finite Λ (Limits.cokernel (C := ModuleCat.{u} Λ) f) :=
      Module.Finite.of_surjective (cokernel.π f).hom
        ((ModuleCat.epi_iff_surjective (cokernel.π f)).1 inferInstance)
    refine ⟨Limits.cokernel (C := ModuleCat.{u} Λ) f, hfin, ⟨?_⟩⟩
    have hcok_ext : cokernel (((u i).smallEtalePullback (ModuleCat.{u} Λ)).map φ) ≅
        cokernel ((constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).map f) :=
      cokernel.mapIso _ _ eF eG (by simp [← hf])
    exact ((u i).smallEtalePullback (ModuleCat.{u} Λ)).mapIso
        (hk.coconePointUniqueUpToIso (cokernelIsCokernel φ)) ≪≫
      PreservesCokernel.iso ((u i).smallEtalePullback (ModuleCat.{u} Λ)) φ ≪≫
      hcok_ext ≪≫
      (PreservesCokernel.iso (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)) f).symm

/-- Over a left Noetherian ring `Λ`, finite lisse étale sheaves of `Λ`-modules are closed under
kernels. -/
instance isClosedUnderKernels_isFiniteLisse [IsNoetherianRing Λ] :
    ObjectProperty.IsClosedUnderKernels
      (IsFiniteLisse : ObjectProperty (Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))) where
  kernels_le := by
    rintro _ ⟨φ, k, hk, hF, hG⟩
    obtain ⟨ι, U, u, hu_et, hu_cov, hφ⟩ := exists_etaleCover_hom_constantSheaf hF hG φ
    refine IsFiniteLisse.of_etaleCover_constantSheaf u hu_cov fun i ↦ ?_
    obtain ⟨M, N, hM, _, eF, eG, f, hf⟩ := hφ i
    have hfin : Module.Finite Λ (Limits.kernel (C := ModuleCat.{u} Λ) f) :=
      (ModuleCat.isFG_iff _).1 ((ModuleCat.isFG Λ).prop_of_mono (kernel.ι f)
        ((ModuleCat.isFG_iff _).2 hM))
    refine ⟨Limits.kernel (C := ModuleCat.{u} Λ) f, hfin, ⟨?_⟩⟩
    have hker_ext : kernel (((u i).smallEtalePullback (ModuleCat.{u} Λ)).map φ) ≅
        kernel ((constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).map f) :=
      kernel.mapIso _ _ eF eG (by simp [← hf])
    exact ((u i).smallEtalePullback (ModuleCat.{u} Λ)).mapIso
        (hk.conePointUniqueUpToIso (kernelIsKernel φ)) ≪≫
      PreservesKernel.iso ((u i).smallEtalePullback (ModuleCat.{u} Λ)) φ ≪≫
      hker_ext ≪≫
      (PreservesKernel.iso (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)) f).symm

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
  let n : Fin a → N := fun k ↦ πN_hom (Pi.single k 1)
  let F₀ : ModuleCat.{u} Λ := ModuleCat.of Λ (Fin a → Λ)
  let πN : F₀ ⟶ N := ModuleCat.ofHom πN_hom
  have hEpiπN : Epi πN := (ModuleCat.epi_iff_surjective πN).2 hn
  let K : ModuleCat.{u} Λ := kernel πN
  have hKfin : Module.Finite Λ K :=
    (ModuleCat.isFG_iff K).1 ((ModuleCat.isFG Λ).prop_of_mono (kernel.ι πN)
      ((ModuleCat.isFG_iff F₀).2 inferInstance))
  let T_S : S.Etale := Etale.mk (𝟙 S)
  let R := ⨅ k : Fin a, Presheaf.imageSieve g.hom
    ((toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj N)).app (op T_S) (n k))
  have hloc : Presheaf.IsLocallySurjective (smallEtaleTopology S) g.hom :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := g)).2 hT.epi_g
  have hR : R ∈ smallEtaleTopology S T_S :=
    iInf_fin_mem_grothendieckTopology (smallEtaleTopology S) _ fun k ↦
      Presheaf.imageSieve_mem (smallEtaleTopology S) g.hom _
  obtain ⟨ι, U, u_cov, hu_et, _, hαR, hcov⟩ :=
    exists_etaleCover_of_mem_smallEtaleTopology_terminal hR
  rw [isFiniteLisse_iff_of_etaleCover E u_cov hcov]
  intro i
  have := hu_et i
  let u : U i ⟶ S := u_cov i
  obtain ⟨αi, hαi⟩ := hαR i
  let T_U : (U i).Etale := Etale.mk (𝟙 (U i))
  let hterm_U : IsTerminal T_U :=
    IsTerminal.isTerminalOfObj (Etale.forget (U i)) _ CategoryTheory.Over.mkIdTerminal
  let E₁ := (u.smallEtalePullback (ModuleCat.{u} Λ)).obj E
  let f₁ : (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).obj M ⟶ E₁ :=
    (u.smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) M).inv ≫
      (u.smallEtalePullback (ModuleCat.{u} Λ)).map f
  let g₁ : E₁ ⟶ (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).obj N :=
    (u.smallEtalePullback (ModuleCat.{u} Λ)).map g ≫
      (u.smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) N).hom
  have hf₁g₁ : f₁ ≫ g₁ = 0 := by
    dsimp [f₁, g₁]
    rw [Category.assoc, ← Category.assoc ((u.smallEtalePullback _).map f), ← Functor.map_comp,
      hfg, Functor.map_zero, zero_comp, comp_zero]
  let T₁ : ShortComplex (Sheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)) :=
    ShortComplex.mk f₁ g₁ hf₁g₁
  have hT₁_iso : ((ShortComplex.mk f g hfg).map (u.smallEtalePullback (ModuleCat.{u} Λ))) ≅ T₁ :=
    ShortComplex.isoMk
      (u.smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) M) (Iso.refl _)
      (u.smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) N)
      (by dsimp [T₁, f₁]; rw [Iso.hom_inv_id_assoc, Category.comp_id])
      (by dsimp [T₁, g₁]; rw [Category.id_comp])
  have hT₁ : T₁.ShortExact :=
    ShortComplex.shortExact_of_iso hT₁_iso (Hom.shortExact_map_smallEtalePullback u hT)
  have hα_mem (k : Fin a) : Presheaf.imageSieve g.hom
      ((toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj N)).app (op T_S) (n k))
      αi := by
    have hle : R ≤ _ := iInf_le _ k
    exact hle _ hαi
  choose s hs using fun k : Fin a ↦ hα_mem k
  let s' : Fin a → E₁.obj.obj (op T_U) := fun k ↦ evalUnitSelf u E (s k)
  let σ₀ : F₀ ⟶ E₁.obj.obj (op T_U) := ModuleCat.ofHom (Fintype.linearCombination Λ s')
  let h : (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).obj F₀ ⟶ E₁ :=
    ((constantSheafAdj (smallEtaleTopology (U i)) (ModuleCat.{u} Λ) hterm_U).homEquiv
      F₀ E₁).symm σ₀
  have hhg₁ : h ≫ g₁ =
      (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).map πN := by
    apply ((constantSheafAdj (smallEtaleTopology (U i))
      (ModuleCat.{u} Λ) hterm_U).homEquiv F₀ _).injective
    rw [Adjunction.homEquiv_naturality_right]
    simp only [h, Equiv.apply_symm_apply]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    simp only [constantSheafAdj, Adjunction.homEquiv_apply, Adjunction.comp_unit_app,
      sheafificationAdjunction_unit_app, constantPresheafAdj_unit_app, Category.id_comp,
      ModuleCat.hom_comp, LinearMap.coe_comp,
      Function.comp_apply, ConcreteCategory.hom_ofHom, σ₀, πN]
    have hc : c = ∑ k : Fin a, c k • Pi.single k (1 : Λ) := by
      ext j
      simp [Pi.single_apply]
    conv_lhs => rw [Fintype.linearCombination_apply, map_sum]
    conv_rhs => rw [hc, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [map_smul]
    refine congrArg (c k • ·) ?_
    have hsk : g.hom.app (op (Etale.mk u)) (s k) =
        (toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj N)).app
          (op (Etale.mk u)) (n k) :=
      (hs k).trans (toSheafify_app_const_map_apply (smallEtaleTopology S) N αi.op (n k))
    have hg_eval := congrArg (evalUnitSelf u
      ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj N)) hsk
    rw [← ConcreteCategory.comp_apply, evalUnitSelf_naturality u g, ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply (g := evalUnitSelf u _), toSheafify_comp_evalUnitSelf,
      ConcreteCategory.comp_apply] at hg_eval
    change (g₁.hom.app (op T_U)) (evalUnitSelf u E (s k)) =
      (((constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).map
        (ModuleCat.ofHom πN_hom)).hom.app (op T_U))
        ((toSheafify (smallEtaleTopology (U i)) ((Functor.const (U i).Etaleᵒᵖ).obj F₀)).app
          (op T_U) (Pi.single k 1))
    dsimp only [g₁, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
    rw [ConcreteCategory.comp_apply, hg_eval, ← ConcreteCategory.comp_apply,
      ← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id]
    simp only [ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
    have hnat := NatTrans.congr_app
      (toSheafify_naturality (smallEtaleTopology (U i))
        ((Functor.const (U i).Etaleᵒᵖ).map (ModuleCat.ofHom πN_hom))) (op T_U)
    exact ConcreteCategory.congr_hom hnat (Pi.single k 1)
  have hkh : ((constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).map (kernel.ι πN) ≫
      h) ≫ g₁ = 0 := by
    rw [Category.assoc, hhg₁, ← Functor.map_comp, kernel.condition, Functor.map_zero]
  let ψ : (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).obj K ⟶
      (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).obj M :=
    (hT₁.fIsKernel.lift (Fork.ofι _ hkh) :)
  have hψf₁ : ψ ≫ f₁ =
      (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).map (kernel.ι πN) ≫
        h :=
    hT₁.fIsKernel.fac (Fork.ofι _ hkh) WalkingParallelPair.zero
  obtain ⟨κ, V, v, _, hv_cov, hψ_loc⟩ := exists_etaleCover_map_constantSheaf (S := U i) ψ
  rw [isFiniteLisse_iff_of_etaleCover E₁ v hv_cov]
  intro j
  obtain ⟨gk, hgk⟩ := hψ_loc j
  let E₂ := ((v j).smallEtalePullback (ModuleCat.{u} Λ)).obj E₁
  let f₂ : (constantSheaf (smallEtaleTopology (V j)) (ModuleCat.{u} Λ)).obj M ⟶ E₂ :=
    ((v j).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) M).inv ≫
      ((v j).smallEtalePullback (ModuleCat.{u} Λ)).map f₁
  let g₂ : E₂ ⟶ (constantSheaf (smallEtaleTopology (V j)) (ModuleCat.{u} Λ)).obj N :=
    ((v j).smallEtalePullback (ModuleCat.{u} Λ)).map g₁ ≫
      ((v j).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) N).hom
  have hf₂g₂ : f₂ ≫ g₂ = 0 := by
    dsimp [f₂, g₂]
    rw [Category.assoc, ← Category.assoc (((v j).smallEtalePullback _).map f₁), ← Functor.map_comp,
      hf₁g₁, Functor.map_zero, zero_comp, comp_zero]
  let T₂ : ShortComplex (Sheaf (smallEtaleTopology (V j)) (ModuleCat.{u} Λ)) :=
    ShortComplex.mk f₂ g₂ hf₂g₂
  have hT₂_iso : T₁.map ((v j).smallEtalePullback (ModuleCat.{u} Λ)) ≅ T₂ :=
    ShortComplex.isoMk
      ((v j).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) M) (Iso.refl _)
      ((v j).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) N)
      (by dsimp [T₁, T₂, f₂]; rw [Iso.hom_inv_id_assoc, Category.comp_id])
      (by dsimp [T₁, T₂, g₂]; rw [Category.id_comp])
  have hT₂ : T₂.ShortExact :=
    ShortComplex.shortExact_of_iso hT₂_iso (Hom.shortExact_map_smallEtalePullback (v j) hT₁)
  let h₂ : (constantSheaf (smallEtaleTopology (V j)) (ModuleCat.{u} Λ)).obj F₀ ⟶ E₂ :=
    ((v j).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) F₀).inv ≫
      ((v j).smallEtalePullback (ModuleCat.{u} Λ)).map h
  have hh₂g₂ : h₂ ≫ g₂ =
      (constantSheaf (smallEtaleTopology (V j)) (ModuleCat.{u} Λ)).map πN := by
    dsimp only [h₂, g₂, Hom.smallEtalePullbackConstantSheafIso, Hom.smallEtalePullback]
    rw [Category.assoc,
      ← Category.assoc (((v j).smallEtaleBaseChange.sheafPullback _ _ _).map h),
      ← Functor.map_comp, hhg₁,
      ← Functor.sheafPullbackConstantSheafIso_inv_naturality_assoc, Iso.inv_hom_id,
      Category.comp_id]
  have hcomm_loc :
      (constantSheaf (smallEtaleTopology (V j)) (ModuleCat.{u} Λ)).map (kernel.ι πN) ≫ h₂ =
        (constantSheaf (smallEtaleTopology (V j)) (ModuleCat.{u} Λ)).map gk ≫ f₂ := by
    calc
      (constantSheaf (smallEtaleTopology (V j)) (ModuleCat.{u} Λ)).map (kernel.ι πN) ≫ h₂
        = ((v j).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) K).inv ≫
            ((v j).smallEtalePullback (ModuleCat.{u} Λ)).map
              ((constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).map
                (kernel.ι πN) ≫ h) := by
          dsimp only [h₂, Hom.smallEtalePullbackConstantSheafIso, Hom.smallEtalePullback]
          rw [Functor.map_comp, ← Category.assoc,
            ← Functor.sheafPullbackConstantSheafIso_inv_naturality_assoc]
          rfl
      _ = ((v j).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) K).inv ≫
            ((v j).smallEtalePullback (ModuleCat.{u} Λ)).map (ψ ≫ f₁) := by rw [hψf₁]
      _ = (((v j).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) K).inv ≫
            ((v j).smallEtalePullback (ModuleCat.{u} Λ)).map ψ ≫
            ((v j).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) M).hom) ≫ f₂ := by
          dsimp [f₂]
          simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
      _ = (constantSheaf (smallEtaleTopology (V j)) (ModuleCat.{u} Λ)).map gk ≫ f₂ := by
          rw [hgk]
  let sq : IsPushout (kernel.ι πN) gk (pushout.inl (kernel.ι πN) gk)
      (pushout.inr (kernel.ι πN) gk) :=
    IsPushout.of_hasPushout (kernel.ι πN) gk
  let S_pres : ShortComplex (ModuleCat.{u} Λ) :=
    ShortComplex.mk (kernel.ι πN) πN (kernel.condition πN)
  have hS_pres : S_pres.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel πN) inferInstance inferInstance
  let P : ModuleCat.{u} Λ := pushout (kernel.ι πN) gk
  let T_mod : ShortComplex (ModuleCat.{u} Λ) :=
    ShortComplex.mk (pushout.inr (kernel.ι πN) gk) (TauCeti.cobaseChangeπ S_pres sq) (by simp)
  have hT_mod : T_mod.ShortExact := TauCeti.shortExact_cobaseChange hS_pres sq
  have hP_fin : Module.Finite Λ P :=
    Module.Finite.of_exact ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T_mod).1
      hT_mod.exact) ((ModuleCat.epi_iff_surjective T_mod.g).1 hT_mod.epi_g)
  let sq_sheaf := (constantSheaf (smallEtaleTopology (V j)) (ModuleCat.{u} Λ)).map_isPushout sq
  let Φ : (constantSheaf (smallEtaleTopology (V j)) (ModuleCat.{u} Λ)).obj P ⟶ E₂ :=
    sq_sheaf.desc h₂ f₂ hcomm_loc
  have hΦ_l : (constantSheaf (smallEtaleTopology (V j)) (ModuleCat.{u} Λ)).map T_mod.f ≫ Φ =
      f₂ :=
    sq_sheaf.inr_desc _ _ _
  have hΦ_r : Φ ≫ g₂ =
      (constantSheaf (smallEtaleTopology (V j)) (ModuleCat.{u} Λ)).map T_mod.g := by
    refine sq_sheaf.hom_ext ?_ ?_
    · rw [← Category.assoc, sq_sheaf.inl_desc, hh₂g₂, ← Functor.map_comp]
      exact congrArg ((constantSheaf (smallEtaleTopology (V j)) (ModuleCat.{u} Λ)).map)
        (TauCeti.inl_cobaseChangeπ S_pres sq).symm
    · rw [← Category.assoc, sq_sheaf.inr_desc, hf₂g₂, ← Functor.map_comp,
        TauCeti.inr_cobaseChangeπ S_pres sq, Functor.map_zero]
  let ψ_sc : T_mod.map (constantSheaf (smallEtaleTopology (V j)) (ModuleCat.{u} Λ)) ⟶ T₂ :=
    { τ₁ := 𝟙 _
      τ₂ := Φ
      τ₃ := 𝟙 _
      comm₁₂ := by simpa [T₂] using hΦ_l.symm
      comm₂₃ := by simpa [T₂] using hΦ_r }
  have hIsoΦ : IsIso Φ :=
    ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ ψ_sc
      (shortExact_map_constantSheaf_smallEtaleTopology Λ hT_mod) hT₂
  exact (isFiniteLisse_constantSheaf P).of_iso (asIso Φ)

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
    let T_i := T.map ((u i).smallEtalePullback (ModuleCat.{u} Λ))
    let f' : (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).obj M ⟶ T_i.X₂ :=
      e₁.inv ≫ T_i.f
    let g' : T_i.X₂ ⟶ (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).obj N :=
      T_i.g ≫ e₃.hom
    have hfg' : f' ≫ g' = 0 := by
      dsimp [f', g']
      rw [Category.assoc, ← Category.assoc T_i.f, T_i.zero, zero_comp, comp_zero]
    let T' : ShortComplex (Sheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)) :=
      ShortComplex.mk f' g' hfg'
    have hT'_iso : T_i ≅ T' :=
      ShortComplex.isoMk e₁ (Iso.refl _) e₃ (by simp [T', f']) (by simp [T', g'])
    have hT' : T'.ShortExact :=
      ShortComplex.shortExact_of_iso hT'_iso (Hom.shortExact_map_smallEtalePullback (u i) hT)
    exact isFiniteLisse_of_shortExact_constantSheaf hT'

end Closure

section DotNotation

variable {S : Scheme.{u}} {Λ : Type u} [Ring Λ]
  {F G : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}

/-- The cokernel of a morphism between finite lisse étale sheaves of `Λ`-modules is finite
lisse, over any ring `Λ`. -/
theorem IsFiniteLisse.cokernel (hF : F.IsFiniteLisse) (hG : G.IsFiniteLisse) (φ : F ⟶ G) :
    (Limits.cokernel φ).IsFiniteLisse :=
  ObjectProperty.prop_cokernel
    (P := (IsFiniteLisse : ObjectProperty (Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))))
    φ hF hG

/-- The kernel of a morphism between finite lisse étale sheaves of `Λ`-modules over a left
Noetherian ring `Λ` is finite lisse. -/
theorem IsFiniteLisse.kernel [IsNoetherianRing Λ] (hF : F.IsFiniteLisse) (hG : G.IsFiniteLisse)
    (φ : F ⟶ G) :
    (Limits.kernel φ).IsFiniteLisse :=
  ObjectProperty.prop_kernel
    (P := (IsFiniteLisse : ObjectProperty (Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))))
    φ hF hG

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
