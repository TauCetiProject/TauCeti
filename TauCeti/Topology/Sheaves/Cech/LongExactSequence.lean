/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Homology
public import TauCeti.Topology.Sheaves.Cech.Flasque
public import TauCeti.Topology.Sheaves.Cech.Sheafification

/-!
# The long exact sequence of Čech cohomology for sheaves on compact spaces

Let `X` be a compact normal space (for instance a compact Hausdorff space) and
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` a short exact sequence of sheaves of modules on `X`. The sequence of
underlying presheaves need not be exact on the right, since sections of `F₃` lift to `F₂` only
locally, so the long exact coefficient sequence of `TauCeti.CategoryTheory.cechCohomologyδ` does
not apply to it directly. It applies to the presheaf cokernel `Q` of `F₁ ⟶ F₂`, and the canonical
map `Q ⟶ F₃` becomes an isomorphism after sheafification. As `Q` vanishes on the empty open, the
map `Q ⟶ F₃` induces isomorphisms on cover-colimit Čech cohomology
(`TauCeti.Topology.isIso_cechCohomology_map_of_isIso_sheafification`). Transporting the presheaf
connecting map along these isomorphisms gives the connecting map
`CategoryTheory.ShortComplex.ShortExact.cechCohomologyδ` and, writing `Hⁿ(X, F)` for the
cover-colimit Čech cohomology, a long exact sequence
`⋯ ⟶ Hⁿ(X, F₂) ⟶ Hⁿ(X, F₃) ⟶ Hⁿ⁺¹(X, F₁) ⟶ Hⁿ⁺¹(X, F₂) ⟶ ⋯`, starting with a monomorphism
in degree `0`.

The connecting map is characterized by its compatibility with the connecting maps of short exact
sequences of presheaves mapping to `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0`
(`CategoryTheory.ShortComplex.ShortExact.cechCohomologyδ_naturality_of_presheaf`), and is natural
in morphisms of short exact sequences of sheaves.

When `F₂` is flasque its higher Čech cohomology vanishes
(`TauCeti.Topology.isZero_cechCohomology_succ_of_isFlasque`), so the connecting map
`Hⁿ(X, F₃) ⟶ Hⁿ⁺¹(X, F₁)` is an isomorphism for `n ≥ 1` and an epimorphism for `n = 0`. Applied
to the embedding of a sheaf in its flasque Godement sheaf, this is the dimension shift used to
compare Čech cohomology with derived-functor cohomology on compact Hausdorff spaces.

## Main definitions

* `CategoryTheory.ShortComplex.ShortExact.cechCohomologyδ`: the connecting map
  `Hⁿ(X, F₃) ⟶ Hⁿ⁺¹(X, F₁)`.

## Main results

* `CategoryTheory.ShortComplex.ShortExact.cechCohomology_exact₁`,
  `CategoryTheory.ShortComplex.ShortExact.cechCohomology_exact₂` and
  `CategoryTheory.ShortComplex.ShortExact.cechCohomology_exact₃`: exactness of the long exact
  sequence at every position, and
  `CategoryTheory.ShortComplex.ShortExact.mono_cechCohomology_map_zero`: its first map is
  monic.
* `CategoryTheory.ShortComplex.ShortExact.cechCohomologyδ_naturality`: naturality in morphisms of
  short exact sequences of sheaves.
* `CategoryTheory.ShortComplex.ShortExact.isIso_cechCohomologyδ_succ_of_isFlasque` and
  `CategoryTheory.ShortComplex.ShortExact.epi_cechCohomologyδ_zero_of_isFlasque`: dimension
  shifting along a short exact sequence with flasque middle term.

## References

* The Stacks Project, Cohomology of Sheaves, Lemma 20.16.2 (tag 09V2), for Čech cohomology of
  sheaves on compact Hausdorff spaces.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace TauCeti.Topology

universe u

namespace CategoryTheory.ShortComplex.ShortExact

variable {X : TopCat.{u}} {R : Type u} [Ring R]
  {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}

/-- The presheaf cokernel `F₁ ⟶ F₂ ⟶ F₂ / F₁` of the first map of a sequence of sheaves. -/
private abbrev presheafCokernelSequence (S : ShortComplex
    (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))) :
    ShortComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) :=
  ShortComplex.mk S.f.hom (cokernel.π S.f.hom) (cokernel.condition _)

/-- The canonical map from the presheaf cokernel of `F₁ ⟶ F₂` to `F₃`. -/
private abbrev cokernelToX₃ (S : ShortComplex
    (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))) :
    cokernel S.f.hom ⟶ S.X₃.obj :=
  cokernel.desc S.f.hom S.g.hom (S.map (sheafToPresheaf _ _)).zero

@[reassoc]
private lemma cokernel_π_cokernelToX₃ (S : ShortComplex
    (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))) :
    cokernel.π S.f.hom ≫ cokernelToX₃ S = S.g.hom :=
  cokernel.π_desc _ _ _

private lemma presheafCokernelSequence_shortExact (hS : S.ShortExact) :
    (presheafCokernelSequence S).ShortExact :=
  have := hS.mono_f
  have : Mono S.f.hom := (sheafToPresheaf _ _).map_mono S.f
  { exact := ShortComplex.exact_cokernel S.f.hom }

private lemma presheafCokernelSequence_map_shortExact (hS : S.ShortExact)
    (U : PointOpenCover X) :
    ((presheafCokernelSequence S).map (cechComplexFunctor U.opens)).ShortExact :=
  (presheafCokernelSequence_shortExact hS).map_of_exact _

/-- The long exact sequence starts with a monomorphism `H⁰(X, F₁) ⟶ H⁰(X, F₂)`. This holds on
every topological space `X`. -/
theorem mono_cechCohomology_map_zero (hS : S.ShortExact) :
    Mono ((cechCohomology X (ModuleCat.{u} R) 0).map S.f.hom) :=
  TauCeti.CategoryTheory.mono_cechCohomology_map_zero (S := presheafCokernelSequence S)
    PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) (presheafCokernelSequence_map_shortExact hS)

variable [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{u} R)]
  [CompactSpace X] [NormalSpace X]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective (ModuleCat.{u} R)]

/-- The map from the presheaf cokernel of `F₁ ⟶ F₂` to `F₃` induces isomorphisms on Čech
cohomology. -/
private lemma isIso_cechCohomology_map_cokernelToX₃ (hS : S.ShortExact) (n : ℕ) :
    IsIso ((cechCohomology X (ModuleCat.{u} R) n).map (cokernelToX₃ S)) := by
  have := hS.isIso_presheafToSheaf_map_cokernelDesc
  refine isIso_cechCohomology_map_of_isIso_sheafification _ ?_ ?_ n
  · exact IsZero.of_epi ((cokernel.π S.f.hom).app (Opposite.op ⊥))
      (TopCat.Sheaf.isTerminalOfEqEmpty S.X₂ rfl).isZero
  · exact (TopCat.Sheaf.isTerminalOfEqEmpty S.X₃ rfl).isZero

/-- **The connecting map of Čech cohomology** for a short exact sequence
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of sheaves of modules on a compact normal space: the map
`Hⁿ(X, F₃) ⟶ Hⁿ⁺¹(X, F₁)`. It is characterized by
`CategoryTheory.ShortComplex.ShortExact.cechCohomologyδ_naturality_of_presheaf`. -/
def cechCohomologyδ (hS : S.ShortExact) (n : ℕ) :
    (cechCohomology X (ModuleCat.{u} R) n).obj S.X₃.obj ⟶
      (cechCohomology X (ModuleCat.{u} R) (n + 1)).obj S.X₁.obj :=
  have := isIso_cechCohomology_map_cokernelToX₃ hS n
  inv ((cechCohomology X (ModuleCat.{u} R) n).map (cokernelToX₃ S)) ≫
    TauCeti.CategoryTheory.cechCohomologyδ (S := presheafCokernelSequence S)
      PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h)
      (presheafCokernelSequence_map_shortExact hS) n

/-- The connecting map of the presheaf cokernel sequence is the sheaf connecting map after the
map induced by `F₂ / F₁ ⟶ F₃`. -/
@[reassoc]
private lemma cechCohomology_map_cokernelToX₃_comp_δ (hS : S.ShortExact) (n : ℕ) :
    (cechCohomology X (ModuleCat.{u} R) n).map (cokernelToX₃ S) ≫ hS.cechCohomologyδ n =
      TauCeti.CategoryTheory.cechCohomologyδ (S := presheafCokernelSequence S)
        PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h)
        (presheafCokernelSequence_map_shortExact hS) n := by
  have := isIso_cechCohomology_map_cokernelToX₃ hS n
  rw [cechCohomologyδ, IsIso.hom_inv_id_assoc]

/-- **Characterization of the connecting map.** For a short exact sequence `T` of presheaves of
modules mapping to the sequence of underlying presheaves of `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0`, the Čech
connecting map of `T` is compatible with that of the sheaves. Taking for `T` the presheaf cokernel
of `F₁ ⟶ F₂` determines `CategoryTheory.ShortComplex.ShortExact.cechCohomologyδ`, as the map
from that cokernel to `F₃` induces isomorphisms on Čech cohomology. -/
@[reassoc]
theorem cechCohomologyδ_naturality_of_presheaf (hS : S.ShortExact)
    {T : ShortComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R)} (hT : T.ShortExact)
    (φ : T ⟶ S.map (sheafToPresheaf _ _)) (n : ℕ) :
    TauCeti.CategoryTheory.cechCohomologyδ (S := T) PointOpenCover.toFormalCoproduct
        (fun _ _ h ↦ h) (fun U : PointOpenCover X ↦ hT.map_of_exact (cechComplexFunctor U.opens))
        n ≫ (cechCohomology X (ModuleCat.{u} R) (n + 1)).map φ.τ₁ =
      (cechCohomology X (ModuleCat.{u} R) n).map φ.τ₃ ≫ hS.cechCohomologyδ n := by
  have := hT.epi_g
  have hk : T.f ≫ φ.τ₂ ≫ cokernel.π S.f.hom = 0 := by
    rw [← reassoc_of% φ.comm₁₂]
    -- the underlying presheaf map `(S.map (sheafToPresheaf _ _)).f` is `S.f.hom`
    exact (φ.τ₁ ≫= cokernel.condition S.f.hom).trans comp_zero
  -- `φ` factors through the presheaf cokernel sequence of `F₁ ⟶ F₂`
  let k := hT.gIsCokernel.desc (CokernelCofork.ofπ _ hk)
  have hgk : T.g ≫ k = φ.τ₂ ≫ cokernel.π S.f.hom :=
    hT.gIsCokernel.fac (CokernelCofork.ofπ _ hk) WalkingParallelPair.one
  let ψ : T ⟶ presheafCokernelSequence S :=
    { τ₁ := φ.τ₁
      τ₂ := φ.τ₂
      τ₃ := k
      comm₁₂ := φ.comm₁₂
      comm₂₃ := hgk.symm }
  have hkc : k ≫ cokernelToX₃ S = φ.τ₃ := by
    rw [← cancel_epi T.g, reassoc_of% hgk, cokernel.π_desc]
    exact φ.comm₂₃
  have h := TauCeti.CategoryTheory.cechCohomologyδ_naturality (S := T)
    PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h)
    (fun U : PointOpenCover X ↦ hT.map_of_exact (cechComplexFunctor U.opens))
    (presheafCokernelSequence_map_shortExact hS) ψ n
  have h' : (cechCohomology X (ModuleCat.{u} R) n).map φ.τ₃ ≫ hS.cechCohomologyδ n =
      (cechCohomology X (ModuleCat.{u} R) n).map ψ.τ₃ ≫
        TauCeti.CategoryTheory.cechCohomologyδ (S := presheafCokernelSequence S)
          PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h)
          (presheafCokernelSequence_map_shortExact hS) n := by
    rw [← hkc, Functor.map_comp, Category.assoc, cechCohomology_map_cokernelToX₃_comp_δ]
  exact h.trans h'.symm

/-- **Naturality of the connecting map** in morphisms of short exact sequences of sheaves. -/
@[reassoc]
theorem cechCohomologyδ_naturality (hS : S.ShortExact)
    {S' : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (hS' : S'.ShortExact) (φ : S ⟶ S') (n : ℕ) :
    hS.cechCohomologyδ n ≫ (cechCohomology X (ModuleCat.{u} R) (n + 1)).map φ.τ₁.hom =
      (cechCohomology X (ModuleCat.{u} R) n).map φ.τ₃.hom ≫ hS'.cechCohomologyδ n := by
  let χ : presheafCokernelSequence S ⟶ S'.map (sheafToPresheaf _ _) :=
    { τ₁ := φ.τ₁.hom
      τ₂ := φ.τ₂.hom
      τ₃ := cokernelToX₃ S ≫ φ.τ₃.hom
      comm₁₂ := congrArg (sheafToPresheaf _ _).map φ.comm₁₂
      comm₂₃ := by
        rw [cokernel.π_desc_assoc]
        exact congrArg (sheafToPresheaf _ _).map φ.comm₂₃ }
  have h := hS'.cechCohomologyδ_naturality_of_presheaf (presheafCokernelSequence_shortExact hS) χ n
  have := isIso_cechCohomology_map_cokernelToX₃ hS n
  rw [← cancel_epi ((cechCohomology X (ModuleCat.{u} R) n).map (cokernelToX₃ S)),
    cechCohomology_map_cokernelToX₃_comp_δ_assoc, ← Functor.map_comp_assoc]
  exact h

/-- The map `Hⁿ(X, F₂) ⟶ Hⁿ(X, F₃)` followed by the connecting map is zero. -/
@[reassoc (attr := simp)]
theorem cechCohomology_comp_δ (hS : S.ShortExact) (n : ℕ) :
    (cechCohomology X (ModuleCat.{u} R) n).map S.g.hom ≫ hS.cechCohomologyδ n = 0 := by
  rw [← cokernel_π_cokernelToX₃, Functor.map_comp, Category.assoc,
    cechCohomology_map_cokernelToX₃_comp_δ]
  exact TauCeti.CategoryTheory.cechCohomology_comp_δ (S := presheafCokernelSequence S)
    PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) (presheafCokernelSequence_map_shortExact hS) n

/-- The connecting map followed by the map `Hⁿ⁺¹(X, F₁) ⟶ Hⁿ⁺¹(X, F₂)` is zero. -/
@[reassoc (attr := simp)]
theorem cechCohomologyδ_comp (hS : S.ShortExact) (n : ℕ) :
    hS.cechCohomologyδ n ≫ (cechCohomology X (ModuleCat.{u} R) (n + 1)).map S.f.hom = 0 := by
  rw [cechCohomologyδ, Category.assoc]
  exact (_ ≫= TauCeti.CategoryTheory.cechCohomologyδ_comp (S := presheafCokernelSequence S)
    PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h)
    (presheafCokernelSequence_map_shortExact hS) n).trans comp_zero

/-- Exactness of `Hⁿ(X, F₁) ⟶ Hⁿ(X, F₂) ⟶ Hⁿ(X, F₃)`. -/
theorem cechCohomology_exact₂ (hS : S.ShortExact) (n : ℕ) :
    (S.map (sheafToPresheaf _ _ ⋙ cechCohomology X (ModuleCat.{u} R) n)).Exact := by
  have := isIso_cechCohomology_map_cokernelToX₃ hS n
  have h := TauCeti.CategoryTheory.cechCohomology_exact₂ (S := presheafCokernelSequence S)
    PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) (presheafCokernelSequence_map_shortExact hS) n
  refine ShortComplex.exact_of_iso ?_ h
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (asIso ((cechCohomology X (ModuleCat.{u} R) n).map (cokernelToX₃ S))) ?_ ?_
  · simp
  · simp [← Functor.map_comp]

/-- Exactness of `Hⁿ(X, F₂) ⟶ Hⁿ(X, F₃) ⟶ Hⁿ⁺¹(X, F₁)`. -/
theorem cechCohomology_exact₃ (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk _ _ (hS.cechCohomology_comp_δ n)).Exact := by
  have := isIso_cechCohomology_map_cokernelToX₃ hS n
  have h := TauCeti.CategoryTheory.cechCohomology_exact₃ (S := presheafCokernelSequence S)
    PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) (presheafCokernelSequence_map_shortExact hS) n
  refine ShortComplex.exact_of_iso ?_ h
  refine ShortComplex.isoMk (Iso.refl _)
    (asIso ((cechCohomology X (ModuleCat.{u} R) n).map (cokernelToX₃ S))) (Iso.refl _) ?_ ?_
  · simp [← Functor.map_comp]
  · simp [cechCohomology_map_cokernelToX₃_comp_δ]

/-- Exactness of `Hⁿ(X, F₃) ⟶ Hⁿ⁺¹(X, F₁) ⟶ Hⁿ⁺¹(X, F₂)`. -/
theorem cechCohomology_exact₁ (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk _ _ (hS.cechCohomologyδ_comp n)).Exact := by
  have := isIso_cechCohomology_map_cokernelToX₃ hS n
  have h := TauCeti.CategoryTheory.cechCohomology_exact₁ (S := presheafCokernelSequence S)
    PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) (presheafCokernelSequence_map_shortExact hS) n
  refine ShortComplex.exact_of_iso ?_ h
  refine ShortComplex.isoMk
    (asIso ((cechCohomology X (ModuleCat.{u} R) n).map (cokernelToX₃ S))) (Iso.refl _)
    (Iso.refl _) ?_ ?_
  · simp [cechCohomology_map_cokernelToX₃_comp_δ]
  · simp

/-- **Dimension shifting.** If the middle term of `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is flasque, the
connecting map `Hⁿ⁺¹(X, F₃) ⟶ Hⁿ⁺²(X, F₁)` is an isomorphism. -/
theorem isIso_cechCohomologyδ_succ_of_isFlasque (hS : S.ShortExact)
    [TopCat.Presheaf.IsFlasque S.X₂.obj] (n : ℕ) :
    IsIso (hS.cechCohomologyδ (n + 1)) := by
  have : Mono (hS.cechCohomologyδ (n + 1)) :=
    (ShortComplex.exact_iff_mono _
      ((isZero_cechCohomology_succ_of_isFlasque S.X₂ n).eq_of_src _ _)).1
      (hS.cechCohomology_exact₃ (n + 1))
  have : Epi (hS.cechCohomologyδ (n + 1)) :=
    (ShortComplex.exact_iff_epi _
      ((isZero_cechCohomology_succ_of_isFlasque S.X₂ (n + 1)).eq_of_tgt _ _)).1
      (hS.cechCohomology_exact₁ (n + 1))
  exact isIso_of_mono_of_epi _

/-- **Dimension shifting in degree zero.** If the middle term of `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is
flasque, the connecting map `H⁰(X, F₃) ⟶ H¹(X, F₁)` is an epimorphism; its kernel is the image of
`H⁰(X, F₂)` (`CategoryTheory.ShortComplex.ShortExact.cechCohomology_exact₃`). -/
theorem epi_cechCohomologyδ_zero_of_isFlasque (hS : S.ShortExact)
    [TopCat.Presheaf.IsFlasque S.X₂.obj] :
    Epi (hS.cechCohomologyδ 0) :=
  (ShortComplex.exact_iff_epi _
    ((isZero_cechCohomology_succ_of_isFlasque S.X₂ 0).eq_of_tgt _ _)).1
    (hS.cechCohomology_exact₁ 0)

end CategoryTheory.ShortComplex.ShortExact
