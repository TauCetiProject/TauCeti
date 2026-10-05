/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.Splitting
public import Mathlib.CategoryTheory.PathCategory.MorphismProperty
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-!
# Extensions from arrow maps

An arrow family `c : HomArrow M N` defines an extension of `M` by `N`: the vertex
spaces are `Nᵢ × Mᵢ`, and an arrow acts by the upper triangular matrix with diagonal
entries `N(a)`, `M(a)` and upper right entry `c(a)`. This extension splits exactly
when `c` belongs to the range of the Hom differential. Changes of vertex splittings
induce isomorphisms fixing both end terms, with explicit composition and inverse formulas.

This gives concrete extensions realizing the obstructions in the cokernel of the Hom
differential, without finiteness or acyclicity assumptions.

## References

H. Derksen and J. Weyman, *An Introduction to Quiver Representations*, Chapter 1,
for the description of extensions by arrow maps modulo changes of vertex splittings.
-/

public section

namespace TauCeti.QuiverRep

open CategoryTheory CategoryTheory.Limits

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]
variable (M N : QuiverRep.{u, v, w, t} k Q)

/-- The representation with arrow matrices `[[N(a), c(a)], [0, M(a)]]`. -/
-- The vertex spaces must reduce to products to type the coordinate API.
@[expose]
noncomputable def arrowExtension (c : HomArrow M N) : QuiverRep.{u, v, w, t} k Q :=
  Paths.lift
    { obj := fun i ↦ ModuleCat.of k (vertexSpace k Q N i × vertexSpace k Q M i)
      map := fun {i j} a ↦ ModuleCat.ofHom
        (((mapₗ k Q N a.toPath).comp (LinearMap.fst k _ _) +
          (c i j a).comp (LinearMap.snd k _ _)).prod
          ((mapₗ k Q M a.toPath).comp (LinearMap.snd k _ _))) }

/-- The vertex spaces of an arrow extension are the products of its end terms. -/
@[simp]
theorem arrowExtension_obj (c : HomArrow M N) (i : Q) :
    (arrowExtension M N c).obj i =
      ModuleCat.of k (vertexSpace k Q N i × vertexSpace k Q M i) := (rfl)

/-- The action of an arrow on an extension, in product coordinates. -/
@[simp]
theorem arrowExtension_map_toPath (c : HomArrow M N) {i j : Q} (a : i ⟶ j)
    (x : vertexSpace k Q N i × vertexSpace k Q M i) :
    (arrowExtension M N c).map a.toPath x =
      (mapₗ k Q N a.toPath x.1 + c i j a x.2, mapₗ k Q M a.toPath x.2) := by
  simp only [arrowExtension, Paths.lift_toPath]
  rfl

/-- Inclusion of the subrepresentation in an arrow extension. -/
noncomputable def arrowExtensionInl (c : HomArrow M N) : N ⟶ arrowExtension M N c :=
  Paths.liftNatTrans (fun i ↦ ModuleCat.ofHom
    (LinearMap.inl k (vertexSpace k Q N i) (vertexSpace k Q M i))) (by
    intro i j a
    exact ModuleCat.hom_ext <| LinearMap.ext fun x ↦ by
      -- Retype the path-category objects as vertices to compute the product coordinates.
      change ((mapₗ k Q N a.toPath) x, 0) =
        ((mapₗ k Q N a.toPath) x + c i j a 0, (mapₗ k Q M a.toPath) 0)
      simp)

/-- Projection of an arrow extension onto its quotient representation. -/
noncomputable def arrowExtensionSnd (c : HomArrow M N) : arrowExtension M N c ⟶ M :=
  Paths.liftNatTrans (fun i ↦ ModuleCat.ofHom
    (LinearMap.snd k (vertexSpace k Q N i) (vertexSpace k Q M i))) (by
    intro i j a
    exact ModuleCat.hom_ext <| LinearMap.ext fun _ ↦ rfl)

@[simp]
theorem arrowExtensionInl_app (c : HomArrow M N) (i : Q) :
    (arrowExtensionInl M N c).app i =
      ModuleCat.ofHom (LinearMap.inl k (vertexSpace k Q N i) (vertexSpace k Q M i)) := (rfl)

@[simp]
theorem arrowExtensionSnd_app (c : HomArrow M N) (i : Q) :
    (arrowExtensionSnd M N c).app i =
      ModuleCat.ofHom (LinearMap.snd k (vertexSpace k Q N i) (vertexSpace k Q M i)) := (rfl)

/-- The inclusion sends a vector to the first factor of the vertex product. -/
@[simp]
theorem arrowExtensionInl_app_apply (c : HomArrow M N) (i : Q)
    (x : vertexSpace k Q N i) :
    ((arrowExtensionInl M N c).app ((Paths.of Q).obj i)).hom x =
      (x, (0 : vertexSpace k Q M i)) := (rfl)

/-- The projection takes the second factor of the vertex product. -/
@[simp]
theorem arrowExtensionSnd_app_apply (c : HomArrow M N) (i : Q)
    (x : vertexSpace k Q N i × vertexSpace k Q M i) :
    ((arrowExtensionSnd M N c).app ((Paths.of Q).obj i)).hom x = x.2 := (rfl)

/-- The short complex `0 → N → E(c) → M → 0` associated to an arrow family. -/
-- The end terms must reduce to `N` and `M` to type its maps and sections.
@[expose]
noncomputable def arrowExtensionComplex (c : HomArrow M N) :
    ShortComplex (QuiverRep.{u, v, w, t} k Q) :=
  ShortComplex.mk (arrowExtensionInl M N c) (arrowExtensionSnd M N c) (by
    ext i x
    rfl)

/-- The associated short complex has the prescribed end terms and maps. -/
@[simp]
theorem arrowExtensionComplex_X₁ (c : HomArrow M N) :
    (arrowExtensionComplex M N c).X₁ = N := (rfl)

@[simp]
theorem arrowExtensionComplex_X₂ (c : HomArrow M N) :
    (arrowExtensionComplex M N c).X₂ = arrowExtension M N c := (rfl)

@[simp]
theorem arrowExtensionComplex_X₃ (c : HomArrow M N) :
    (arrowExtensionComplex M N c).X₃ = M := (rfl)

@[simp]
theorem arrowExtensionComplex_f (c : HomArrow M N) :
    (arrowExtensionComplex M N c).f = arrowExtensionInl M N c := (rfl)

@[simp]
theorem arrowExtensionComplex_g (c : HomArrow M N) :
    (arrowExtensionComplex M N c).g = arrowExtensionSnd M N c := (rfl)

/-- Every arrow family gives a short exact sequence of representations. -/
theorem arrowExtensionComplex_shortExact (c : HomArrow M N) :
    (arrowExtensionComplex M N c).ShortExact := by
  have h : JointlyReflectIsomorphisms
      (fun i : Paths Q ↦ (evaluation (Paths Q) (ModuleCat k)).obj i) :=
    ⟨fun f _ ↦ by
      have : ∀ i, IsIso (f.app i) := fun i ↦ inferInstanceAs
        (IsIso (((evaluation (Paths Q) (ModuleCat k)).obj i).map f))
      exact NatIso.isIso_of_isIso_app f⟩
  have hv (i : Q) : ((arrowExtensionComplex M N c).map
      ((evaluation (Paths Q) (ModuleCat k)).obj ((Paths.of Q).obj i))).ShortExact := by
    exact (show ((arrowExtensionComplex M N c).map
        ((evaluation (Paths Q) (ModuleCat k)).obj ((Paths.of Q).obj i))).Splitting from
      { r := (ModuleCat.ofHom (LinearMap.fst k (vertexSpace k Q N i) (vertexSpace k Q M i)) :
          ModuleCat.of k (vertexSpace k Q N i × vertexSpace k Q M i) ⟶ N.obj i)
        s := (ModuleCat.ofHom (LinearMap.inr k (vertexSpace k Q N i) (vertexSpace k Q M i)) :
          M.obj i ⟶ ModuleCat.of k (vertexSpace k Q N i × vertexSpace k Q M i))
        f_r := by ext x; rfl
        s_g := by ext x; rfl
        id := by
          apply ModuleCat.hom_ext
          refine LinearMap.ext fun (x : vertexSpace k Q N i × vertexSpace k Q M i) ↦ ?_
          -- Evaluation retypes the vertices; expose just the product-coordinate equality.
          change (x.1 + (0 : vertexSpace k Q N i), (0 : vertexSpace k Q M i) + x.2) = x
          exact Prod.ext (add_zero _) (zero_add _) }).shortExact
  exact (h.shortExact_iff _).mpr fun i ↦ hv i

/-- A change of vertex splittings induces a map between the corresponding extensions,
fixing both end terms. -/
noncomputable def arrowExtensionHom (c c' : HomArrow M N) (h : HomVertex M N)
    (hh : homDifferential M N h = c - c') :
    arrowExtension M N c ⟶ arrowExtension M N c' :=
  Paths.liftNatTrans (fun i ↦ ModuleCat.ofHom
    (((LinearMap.fst k _ _) + (h i).comp (LinearMap.snd k _ _)).prod
      (LinearMap.snd k _ _))) (by
    intro i j a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun d ↦ d i j a x.2) hh
    simp only [homDifferential_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      Pi.sub_apply] at hx
    -- Path-category objects are retyped as vertices to expose the product coordinates.
    change vertexSpace k Q N i × vertexSpace k Q M i at x
    change (((arrowExtension M N c).map a.toPath x).1 +
        h j ((arrowExtension M N c).map a.toPath x).2,
        ((arrowExtension M N c).map a.toPath x).2) =
      (arrowExtension M N c').map a.toPath (x.1 + h i x.2, x.2)
    simp only [arrowExtension_map_toPath]
    apply Prod.ext
    · rw [map_add]
      have hc := (sub_eq_sub_iff_add_eq_add).mp hx
      grind only
    · rfl)

/-- The change of splittings acts by an upper triangular matrix with identity diagonal. -/
@[simp]
theorem arrowExtensionHom_app_apply (c c' : HomArrow M N) (h : HomVertex M N)
    (hh : homDifferential M N h = c - c') (i : Q)
    (x : vertexSpace k Q N i × vertexSpace k Q M i) :
    ((arrowExtensionHom M N c c' h hh).app ((Paths.of Q).obj i)).hom x =
      (x.1 + h i x.2, x.2) := (rfl)

/-- A change of splittings fixes the inclusion of the subrepresentation. -/
@[reassoc (attr := simp)]
theorem arrowExtensionInl_arrowExtensionHom (c c' : HomArrow M N) (h : HomVertex M N)
    (hh : homDifferential M N h = c - c') :
    arrowExtensionInl M N c ≫ arrowExtensionHom M N c c' h hh =
      arrowExtensionInl M N c' := by
  apply NatTrans.ext
  funext i
  apply ModuleCat.hom_ext
  ext x
  -- Retype the path-category vertex so the component API applies.
  change Q at i
  change vertexSpace k Q N i at x
  -- The composite is retyped between the fixed end terms before rewriting.
  change ((arrowExtensionHom M N c c' h hh).app ((Paths.of Q).obj i)).hom
    (((arrowExtensionInl M N c).app ((Paths.of Q).obj i)).hom x) =
      ((arrowExtensionInl M N c').app ((Paths.of Q).obj i)).hom x
  rw [arrowExtensionInl_app_apply, arrowExtensionInl_app_apply, arrowExtensionHom_app_apply]
  simp only [map_zero, add_zero]
  rfl

/-- A change of splittings fixes the projection to the quotient representation. -/
@[reassoc (attr := simp)]
theorem arrowExtensionHom_arrowExtensionSnd (c c' : HomArrow M N) (h : HomVertex M N)
    (hh : homDifferential M N h = c - c') :
    arrowExtensionHom M N c c' h hh ≫ arrowExtensionSnd M N c' =
      arrowExtensionSnd M N c := by
  apply NatTrans.ext
  funext i
  apply ModuleCat.hom_ext
  ext x
  -- Retype the path-category vertex so the component API applies.
  change Q at i
  change vertexSpace k Q N i × vertexSpace k Q M i at x
  -- The composite is retyped between the fixed end terms before rewriting.
  change ((arrowExtensionSnd M N c').app ((Paths.of Q).obj i)).hom
    (((arrowExtensionHom M N c c' h hh).app ((Paths.of Q).obj i)).hom x) =
      ((arrowExtensionSnd M N c).app ((Paths.of Q).obj i)).hom x
  rw [arrowExtensionSnd_app_apply, arrowExtensionHom_app_apply,
    arrowExtensionSnd_app_apply]

/-- A morphism from an arrow extension to a short exact sequence, fixing both
end terms, is an isomorphism. -/
theorem isIso_of_arrowExtension_fixing_ends
    {S : ShortComplex (QuiverRep.{u, v, w, t} k Q)} (hS : S.ShortExact)
    (c : HomArrow S.X₃ S.X₁) (α : arrowExtension S.X₃ S.X₁ c ⟶ S.X₂)
    (hf : arrowExtensionInl S.X₃ S.X₁ c ≫ α = S.f)
    (hg : α ≫ S.g = arrowExtensionSnd S.X₃ S.X₁ c) : IsIso α := by
  let φ : arrowExtensionComplex S.X₃ S.X₁ c ⟶ S :=
    { τ₁ := 𝟙 S.X₁
      τ₂ := α
      τ₃ := 𝟙 S.X₃
      comm₁₂ := (Category.id_comp _).trans hf.symm
      comm₂₃ := hg.trans (Category.comp_id _).symm }
  have : IsIso φ.τ₁ := inferInstanceAs (IsIso (𝟙 S.X₁))
  have : IsIso φ.τ₃ := inferInstanceAs (IsIso (𝟙 S.X₃))
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ
    (arrowExtensionComplex_shortExact S.X₃ S.X₁ c) hS

/-- Every change of splittings is an isomorphism of extensions. -/
instance isIso_arrowExtensionHom (c c' : HomArrow M N) (h : HomVertex M N)
    (hh : homDifferential M N h = c - c') :
    IsIso (arrowExtensionHom M N c c' h hh) :=
  isIso_of_arrowExtension_fixing_ends (arrowExtensionComplex_shortExact M N c') c
    (arrowExtensionHom M N c c' h hh)
    (arrowExtensionInl_arrowExtensionHom M N c c' h hh)
    (arrowExtensionHom_arrowExtensionSnd M N c c' h hh)

/-- Composing changes of vertex splittings adds their vertex families. -/
@[simp]
theorem arrowExtensionHom_comp (c c' c'' : HomArrow M N) (h h' : HomVertex M N)
    (hh : homDifferential M N h = c - c')
    (hh' : homDifferential M N h' = c' - c'') :
    arrowExtensionHom M N c c' h hh ≫ arrowExtensionHom M N c' c'' h' hh' =
      arrowExtensionHom M N c c'' (h + h') (by rw [map_add, hh, hh']; abel) := by
  ext i x
  -- Retype the path vertex and composite so the component API matches.
  change Q at i
  change vertexSpace k Q N i × vertexSpace k Q M i at x
  change ((arrowExtensionHom M N c' c'' h' hh').app ((Paths.of Q).obj i)).hom
      (((arrowExtensionHom M N c c' h hh).app ((Paths.of Q).obj i)).hom x) =
    ((arrowExtensionHom M N c c'' (h + h') _).app ((Paths.of Q).obj i)).hom x
  rw [arrowExtensionHom_app_apply, arrowExtensionHom_app_apply, arrowExtensionHom_app_apply]
  simp only [Pi.add_apply, LinearMap.add_apply, add_assoc]
  rfl

/-- A zero change of vertex splittings is the identity. -/
@[simp]
theorem arrowExtensionHom_zero (c : HomArrow M N) :
    arrowExtensionHom M N c c 0 (by simp) = 𝟙 _ := by
  ext i x
  -- Retype the path vertex so the component API matches.
  change Q at i
  change vertexSpace k Q N i × vertexSpace k Q M i at x
  change ((arrowExtensionHom M N c c 0 _).app ((Paths.of Q).obj i)).hom x = x
  rw [arrowExtensionHom_app_apply]
  simp only [Pi.zero_apply, LinearMap.zero_apply, add_zero]
  rfl

/-- The inverse change of vertex splittings negates the vertex family. -/
@[simp]
theorem inv_arrowExtensionHom (c c' : HomArrow M N) (h : HomVertex M N)
    (hh : homDifferential M N h = c - c') :
    inv (arrowExtensionHom M N c c' h hh) =
      arrowExtensionHom M N c' c (-h) (by rw [map_neg, hh, neg_sub]) := by
  apply IsIso.inv_eq_of_hom_inv_id
  rw [arrowExtensionHom_comp]
  simp

/-- The zero arrow family has the canonical section into the second vertex factor. -/
noncomputable def arrowExtensionSection : M ⟶ arrowExtension M N 0 :=
  Paths.liftNatTrans (fun i ↦ ModuleCat.ofHom
    (LinearMap.inr k (vertexSpace k Q N i) (vertexSpace k Q M i))) (by
    intro i j a
    apply ModuleCat.hom_ext
    ext x
    -- Retype the path objects to apply the arrow-action formula.
    change vertexSpace k Q M i at x
    change (0, mapₗ k Q M a.toPath x) = (arrowExtension M N 0).map a.toPath (0, x)
    simp only [arrowExtension_map_toPath, Pi.zero_apply, LinearMap.zero_apply, map_zero,
      add_zero])

/-- The canonical section of the zero arrow extension is inclusion in the second factor. -/
@[simp]
theorem arrowExtensionSection_app_apply (i : Q) (x : vertexSpace k Q M i) :
    ((arrowExtensionSection M N).app ((Paths.of Q).obj i)).hom x =
      ((0 : vertexSpace k Q N i), x) := (rfl)

/-- The canonical section is a right inverse to the projection. -/
@[reassoc (attr := simp)]
theorem arrowExtensionSection_arrowExtensionSnd :
    arrowExtensionSection M N ≫ arrowExtensionSnd M N 0 = 𝟙 M := by
  ext i x
  rfl

/-- An arrow extension splits exactly when its arrow family is a coboundary. -/
@[simp]
theorem nonempty_splitting_arrowExtensionComplex_iff (c : HomArrow M N) :
    Nonempty (arrowExtensionComplex M N c).Splitting ↔
      c ∈ (homDifferential M N).range := by
  constructor
  · rintro ⟨sp⟩
    let s := sp.s
    let h : HomVertex M N := fun i ↦
      -(LinearMap.fst k (vertexSpace k Q N i) (vertexSpace k Q M i)).comp (s.app i).hom
    refine ⟨h, ?_⟩
    have hs (i : Q) (x : vertexSpace k Q M i) : ((s.app i).hom x).2 = x :=
      congrArg (fun f ↦ (f.app i).hom x) sp.s_g
    ext i j a x
    have hn : (mapₗ k Q N a.toPath) ((s.app i).hom x).1 +
        c i j a ((s.app i).hom x).2 =
          ((s.app j).hom ((mapₗ k Q M a.toPath) x)).1 :=
      congrArg Prod.fst
        (congrArg (fun f ↦ f.hom x) (s.naturality ((Paths.of Q).map a))).symm
    simp only [hs i x] at hn
    refine (congrArg (fun f ↦ f x) (homDifferential_apply M N h a)).trans ?_
    -- The section's categorical domain is a path object; retype its coordinates as vertices.
    change (mapₗ k Q N a.toPath) (-((s.app i).hom x).1) -
      (-((s.app j).hom ((mapₗ k Q M a.toPath) x)).1) = c i j a x
    rw [map_neg, ← hn]
    abel
  · rintro ⟨h, hh⟩
    let s := arrowExtensionSection M N ≫ arrowExtensionHom M N 0 c (-h)
      (by rw [map_neg, hh]; simp)
    have hsg : s ≫ (arrowExtensionComplex M N c).g = 𝟙 M := by
      -- Retype the complex endpoints as representations before rewriting the composite.
      change (arrowExtensionSection M N ≫ arrowExtensionHom M N 0 c (-h) _) ≫
        arrowExtensionSnd M N c = 𝟙 M
      rw [Category.assoc, arrowExtensionHom_arrowExtensionSnd,
        arrowExtensionSection_arrowExtensionSnd]
    exact ⟨ShortComplex.Splitting.ofExactOfSection _
      (arrowExtensionComplex_shortExact M N c).exact s hsg
      (arrowExtensionComplex_shortExact M N c).mono_f⟩

end TauCeti.QuiverRep
