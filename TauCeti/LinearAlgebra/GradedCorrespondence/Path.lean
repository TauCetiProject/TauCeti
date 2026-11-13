/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.GradedCorrespondence.Hom
public import Mathlib.Algebra.Category.ModuleCat.Semi
public import Mathlib.CategoryTheory.PathCategory.MorphismProperty

/-!
# Homogeneous transfer along admissible paths

Choose a homogeneous piece at each vertex of a quiver and a graded
correspondence on each arrow. Their transfers extend to a functor from the free
path category to semimodules. Thus a finite admissible itinerary has a linear
propagation map, with concatenation given by composition in traversal order.
Vertices may represent occurrences of a chamber with different selected degrees;
neither the quiver nor its sets of arrows need to be finite.

Morphisms of the edge correspondences over vertexwise degree maps, with a common
chamber map at incident edges, induce a natural transformation of the transfer
functors when the output degree maps are injective.
This proves compatibility along arbitrary admissible sequences, including coefficient
truncations. It does not assert invertibility of a selected homogeneous component.

Each arrow has independent left and right admissible sets. Only its source degree
must be admissible on its left side. A terminal vertex needs no lift,
so its selected degree may lie outside the admissible set. The prefunctor and functor
bodies are exposed to compute their object types; value calculations use the public
object, edge, and natural-transformation component lemmas below.

The construction uses Mathlib's `Paths.lift`; its one-step naturality is
`GradedCorrespondence.Hom.transfer_map_of_injective`. Only the source degree
selected at each arrow must be admissible; admissibility need not be reflected.

Adapted from `Mei/LinearAlgebra/GradedCorrespondence/Path.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public section

open CategoryTheory

namespace TauCeti.GradedCorrespondence

universe v

variable {R Q : Type*} [Semiring R] [Quiver Q]
  {M : Q → Type v} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)]
  (𝒜 : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (𝒜 q)]
  {I : ∀ {u v : Q}, (u ⟶ v) → Set (ι u)}
  {J : ∀ {u v : Q}, (u ⟶ v) → Set (ι v)}
  {B : ∀ {u v : Q}, (u ⟶ v) → Type*}
  [∀ (u v : Q) (e : u ⟶ v), AddCommMonoid (B e)]
  [∀ (u v : Q) (e : u ⟶ v), Module R (B e)]
  (C : ∀ {u v : Q} (e : u ⟶ v),
    GradedCorrespondence (B := B e) (𝒜 u) (𝒜 v) (I e) (J e))
  (p : ∀ q, ι q)
  (hp : ∀ {u v : Q} (e : u ⟶ v), p u ∈ I e)

/-- Select one homogeneous transfer on every arrow of an admissible itinerary quiver. -/
@[expose]
noncomputable def transferPrefunctor : Q ⥤q SemimoduleCat R where
  obj q := SemimoduleCat.of R (𝒜 q (p q))
  map {u v} e := SemimoduleCat.ofHom ((C e).transfer ⟨p u, hp e⟩ (p v))

/-- The selected homogeneous module at a vertex. -/
@[simp]
theorem transferPrefunctor_obj (q : Q) :
    (transferPrefunctor 𝒜 C p hp).obj q = SemimoduleCat.of R (𝒜 q (p q)) := rfl

/-- Each edge is sent to its selected homogeneous transfer. -/
@[simp]
theorem transferPrefunctor_map {u v : Q} (e : u ⟶ v) :
    (transferPrefunctor 𝒜 C p hp).map e =
      SemimoduleCat.ofHom ((C e).transfer ⟨p u, hp e⟩ (p v)) := rfl

/-- Homogeneous propagation along finite paths, freely extending the single-step transfers. -/
@[expose]
noncomputable def transferFunctor : Paths Q ⥤ SemimoduleCat R :=
  Paths.lift (transferPrefunctor 𝒜 C p hp)

/-- Path propagation uses the selected homogeneous module as its vertex object. -/
@[simp]
theorem transferFunctor_obj (q : Q) :
    (transferFunctor 𝒜 C p hp).obj q =
      SemimoduleCat.of R (𝒜 q (p q)) := rfl

/-- The linear map of a one-edge path is the correspondence's chosen component. -/
@[simp]
theorem transferFunctor_map_toPath_hom {u v : Q} (e : u ⟶ v) :
    ((transferFunctor 𝒜 C p hp).map e.toPath).hom =
      (C e).transfer ⟨p u, hp e⟩ (p v) := by
  exact congrArg SemimoduleCat.Hom.hom
    (Paths.lift_toPath (transferPrefunctor 𝒜 C p hp) e)

section Naturality

variable {M' : Q → Type v} [∀ q, AddCommMonoid (M' q)] [∀ q, Module R (M' q)]
  {κ : Q → Type*} [∀ q, DecidableEq (κ q)]
  (𝒜' : ∀ q, κ q → Submodule R (M' q)) [∀ q, DirectSum.Decomposition (𝒜' q)]
  {B' : ∀ {u v : Q}, (u ⟶ v) → Type*}
  [∀ (u v : Q) (e : u ⟶ v), AddCommMonoid (B' e)]
  [∀ (u v : Q) (e : u ⟶ v), Module R (B' e)]
  {I' : ∀ {u v : Q}, (u ⟶ v) → Set (κ u)}
  {J' : ∀ {u v : Q}, (u ⟶ v) → Set (κ v)}
  (D : ∀ {u v : Q} (e : u ⟶ v),
    GradedCorrespondence (B := B' e) (𝒜' u) (𝒜' v) (I' e) (J' e))
  (r : ∀ q, M q →ₗ[R] M' q) (σ : ∀ q, ι q → κ q)
  (hr : ∀ q i a, a ∈ 𝒜 q i → r q a ∈ 𝒜' q (σ q i))
  (hσ : ∀ {u v : Q} (_ : u ⟶ v), Function.Injective (σ v))

variable
  (f : ∀ {u v : Q} (e : u ⟶ v), Hom (C e) (D e) (σ u) (σ v))
  (hl : ∀ {u v : Q} (e : u ⟶ v), (f e).left = r u)
  (hv : ∀ {u v : Q} (e : u ⟶ v), (f e).right = r v)

include f hl hv hσ

/-- Chamber maps intertwine a selected homogeneous transfer at every crossing. -/
private theorem restrict_transfer {u v : Q} (e : u ⟶ v) :
    ((r v).restrict (hr v (p v))).comp ((C e).transfer ⟨p u, hp e⟩ (p v)) =
      ((D e).transfer ⟨σ u (p u), (f e).admissible_left (hp e)⟩ (σ v (p v))).comp
        ((r u).restrict (hr u (p u))) := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  have he := (f e).transfer_map_of_injective (hσ e) ⟨p u, hp e⟩ a (p v)
  simpa only [LinearMap.comp_apply, LinearMap.coe_restrict_apply,
    LinearMap.restrict_apply, transfer_apply, id_eq, hl e, hv e] using he.symm

/-- Correspondence morphisms intertwine selected propagation along every finite
admissible sequence under injective output regradings. Degree types and admissible
sets may differ at every vertex. No reflection of admissibility or injectivity of
coefficient maps is required. Identity degree maps recover coefficient truncation. -/
noncomputable def transferNatTrans :
    transferFunctor 𝒜 C p hp ⟶
      transferFunctor 𝒜' D (fun q => σ q (p q)) (fun {_ _} e ↦ (f e).admissible_left (hp e)) :=
  Paths.liftNatTrans
    (fun q ↦ SemimoduleCat.ofHom ((r q).restrict (hr q (p q)))) (by
      intro u v e
      apply SemimoduleCat.hom_ext
      have hleft : ((transferFunctor 𝒜 C p hp).map e.toPath ≫
          SemimoduleCat.ofHom ((r v).restrict (hr v (p v)))).hom =
          ((r v).restrict (hr v (p v))).comp ((C e).transfer ⟨p u, hp e⟩ (p v)) :=
        (SemimoduleCat.hom_comp _ _).trans
          (congrArg₂ LinearMap.comp (SemimoduleCat.hom_ofHom _)
            (transferFunctor_map_toPath_hom 𝒜 C p hp e))
      have hright : (SemimoduleCat.ofHom ((r u).restrict (hr u (p u))) ≫
          (transferFunctor 𝒜' D (fun q => σ q (p q))
            (fun {_ _} e ↦ (f e).admissible_left (hp e))).map e.toPath).hom =
          ((D e).transfer ⟨σ u (p u), (f e).admissible_left (hp e)⟩ (σ v (p v))).comp
            ((r u).restrict (hr u (p u))) :=
        (SemimoduleCat.hom_comp _ _).trans
          (congrArg₂ LinearMap.comp
            (transferFunctor_map_toPath_hom 𝒜' D (fun q => σ q (p q))
              (fun {_ _} e ↦ (f e).admissible_left (hp e)) e)
            (SemimoduleCat.hom_ofHom _))
      exact hleft.trans ((restrict_transfer 𝒜 C p hp 𝒜' D r σ hr hσ f hl hv e).trans hright.symm))

/-- A component of the propagation comparison is the restricted chamber map. -/
@[simp]
theorem transferNatTrans_app_hom (q : Q) :
    ((transferNatTrans 𝒜 C p hp 𝒜' D r σ hr hσ f hl hv).app q).hom =
      (r q).restrict (hr q (p q)) := (rfl)

end Naturality

end TauCeti.GradedCorrespondence
