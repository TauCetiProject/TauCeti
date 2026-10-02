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
when `c` belongs to the range of the Hom differential. Consequently that differential
is surjective if and only if every extension of `M` by `N` splits.

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
    let s : M ⟶ arrowExtension M N c := Paths.liftNatTrans
      (fun i ↦ ModuleCat.ofHom ((-h i).prod (LinearMap.id :
        vertexSpace k Q M i →ₗ[k] vertexSpace k Q M i))) (by
        intro i j a
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        have hx : (mapₗ k Q N a.toPath) (h i x) -
            h j ((mapₗ k Q M a.toPath) x) = c i j a x :=
          (congrArg (fun f ↦ f x) (homDifferential_apply M N h a)).symm.trans
            (congrArg (fun d ↦ d i j a x) hh)
        -- Compute the triangular arrow matrix, retyping path objects as vertices.
        change (-h j ((mapₗ k Q M a.toPath) x), (mapₗ k Q M a.toPath) x) =
          ((mapₗ k Q N a.toPath) (-h i x) + c i j a x, (mapₗ k Q M a.toPath) x)
        apply Prod.ext
        · simp only [map_neg]
          rw [← hx]
          abel
        · rfl)
    have hsg : s ≫ (arrowExtensionComplex M N c).g = 𝟙 M := by
      ext i x
      rfl
    exact ⟨ShortComplex.Splitting.ofExactOfSection _
      (arrowExtensionComplex_shortExact M N c).exact s hsg
      (arrowExtensionComplex_shortExact M N c).mono_f⟩

/-- The Hom differential is surjective if and only if every short exact sequence with
quotient `M` and subrepresentation `N` splits. -/
theorem homDifferential_surjective_iff_all_extensions_split :
    Function.Surjective (homDifferential M N) ↔
      ∀ (E : QuiverRep.{u, v, w, t} k Q) (f : N ⟶ E) (g : E ⟶ M)
        (hfg : f ≫ g = 0), (ShortComplex.mk f g hfg).ShortExact →
          Nonempty (ShortComplex.mk f g hfg).Splitting := by
  constructor
  · intro h E f g hfg hS
    exact TauCeti.nonempty_splitting_of_surjective_homDifferential hS h
  · intro h c
    have hs := h _ (arrowExtensionInl M N c) (arrowExtensionSnd M N c)
      (arrowExtensionComplex M N c).zero (arrowExtensionComplex_shortExact M N c)
    exact (nonempty_splitting_arrowExtensionComplex_iff M N c).mp hs

end TauCeti.QuiverRep
