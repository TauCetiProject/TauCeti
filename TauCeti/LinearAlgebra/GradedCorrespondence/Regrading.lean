/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.GradedCorrespondence.History

/-!
# Regrading admissible transfer histories

Correspondence morphisms with injective output degree maps transport the whole
coefficient of a selected admissible history along an arbitrary path. The chamber
modules and their degree types may vary between vertices and between the two
coefficient systems. The comparison is an identity of linear maps on the incoming
homogeneous piece, hence works simultaneously for every incoming coefficient.

Unlike comparison of zero-extended total transfers on mixed inputs, this needs no
reflection of admissibility and no condition on inadmissible source pieces. Only
the selected degree at each crossing has to be admissible. Injectivity of the
terminal chamber map on the selected output piece reflects vanishing. Applying
the same theorem to prefixes retains all nonzero intermediate decorations, as
needed when lifting coefficient histories.

The proof uses `GradedCorrespondence.transferNatTrans` and the identification
`GradedCorrespondence.transferFunctor_map_hom_eq_homogeneousHistory`. The
whole-component interpretation follows Gross–Hacking–Siebert, *Theta functions
on varieties with effective anti-canonical class*, Definitions 3.1–3.3
(arXiv:1601.07081v4).

Adapted from `Mei/LinearAlgebra/GradedCorrespondence/History/Regrading.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public noncomputable section

universe v

namespace TauCeti.GradedCorrespondence

variable {R Q : Type*} [Semiring R] [Quiver Q]
  {M N : Q → Type v} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  [∀ q, AddCommMonoid (N q)] [∀ q, Module R (N q)]
  {ι κ : Q → Type*} [∀ q, DecidableEq (ι q)] [∀ q, DecidableEq (κ q)]
  (ℳ : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (ℳ q)]
  (𝓝 : ∀ q, κ q → Submodule R (N q)) [∀ q, DirectSum.Decomposition (𝓝 q)]
  {B B' : ∀ {b c : Q}, (b ⟶ c) → Type*}
  [∀ (b c : Q) (e : b ⟶ c), AddCommMonoid (B e)]
  [∀ (b c : Q) (e : b ⟶ c), Module R (B e)]
  [∀ (b c : Q) (e : b ⟶ c), AddCommMonoid (B' e)]
  [∀ (b c : Q) (e : b ⟶ c), Module R (B' e)]
  {I : ∀ {b c : Q}, (b ⟶ c) → Set (ι b)}
  {J : ∀ {b c : Q}, (b ⟶ c) → Set (ι c)}
  {I' : ∀ {b c : Q}, (b ⟶ c) → Set (κ b)}
  {J' : ∀ {b c : Q}, (b ⟶ c) → Set (κ c)}
  (C : ∀ {b c : Q} (e : b ⟶ c),
    GradedCorrespondence (B := B e) (ℳ b) (ℳ c) (I e) (J e))
  (D : ∀ {b c : Q} (e : b ⟶ c),
    GradedCorrespondence (B := B' e) (𝓝 b) (𝓝 c) (I' e) (J' e))
  (r : ∀ q, M q →ₗ[R] N q) (σ : ∀ q, ι q → κ q)
  (hr : ∀ q i x, x ∈ ℳ q i → r q x ∈ 𝓝 q (σ q i))
  (hσ : ∀ {b c : Q} (_ : b ⟶ c), Function.Injective (σ c))
  (F : ∀ {b c : Q} (e : b ⟶ c), Hom (C e) (D e) (σ b) (σ c))
  (hleft : ∀ {b c : Q} (e : b ⟶ c), (F e).left = r b)
  (hright : ∀ {b c : Q} (e : b ⟶ c), (F e).right = r c)
  (s : ∀ q, ι q) (hs : ∀ {b c : Q} (e : b ⟶ c), s b ∈ I e)

local notation "T" => fun e => totalTransfer (C e)
local notation "U" => fun e => totalTransfer (D e)
local notation "s'" => fun q => σ q (s q)

include hσ F hleft hright hs

/-- Admissible selected histories intertwine under regrading as linear maps on
an incoming homogeneous piece. No condition on inadmissible pieces is imposed. -/
theorem map_homogeneousHistory_totalTransfer_of_admissible {a b : Q}
    (p : Quiver.Path a b) :
    (r b).comp ((p.homogeneousHistory T ℳ (p.degreesOfVertices s)).comp
      (ℳ a (s a)).subtype) =
    (p.homogeneousHistory U 𝓝 (p.degreesOfVertices s')).comp
      ((𝓝 a (s' a)).subtype.comp ((r a).restrict (hr a (s a)))) := by
  let η := transferNatTrans ℳ C s hs 𝓝 D r σ hr hσ F hleft hright
  have hnat := congrArg SemimoduleCat.Hom.hom (η.naturality p)
  simp only [η, SemimoduleCat.hom_comp, transferNatTrans_app_hom] at hnat
  ext x
  have hsource := LinearMap.congr_fun
    (transferFunctor_map_hom_eq_homogeneousHistory ℳ C s hs p) x
  have htarget := LinearMap.congr_fun
    (transferFunctor_map_hom_eq_homogeneousHistory 𝓝 D s'
      (fun {_ _} e => (F e).admissible_left (hs e)) p) ((r a).restrict (hr a (s a)) x)
  have he := congrArg Subtype.val (LinearMap.congr_fun hnat x)
  simp only [LinearMap.comp_apply, LinearMap.restrict_apply, Submodule.subtype_apply]
    at hsource htarget he ⊢
  exact (congrArg (r b) hsource).symm.trans (he.trans htarget)

/-- An embedding on the selected terminal piece reflects which admissible
histories survive. Injectivity on the other chamber modules is unnecessary. -/
theorem homogeneousHistory_totalTransfer_eq_zero_iff_of_admissible {a b : Q}
    (p : Quiver.Path a b)
    (hinj : Function.Injective ((r b).restrict (hr b (s b)))) (x : ℳ a (s a)) :
    p.homogeneousHistory U 𝓝 (p.degreesOfVertices s') (r a x) = 0 ↔
      p.homogeneousHistory T ℳ (p.degreesOfVertices s) x = 0 := by
  have hsource := transferFunctor_map_hom_eq_homogeneousHistory ℳ C s hs p
  have hmem : p.homogeneousHistory T ℳ (p.degreesOfVertices s) x ∈ ℳ b (s b) := by
    have he := LinearMap.congr_fun hsource x
    exact he ▸ (((transferFunctor ℳ C s hs).map p).hom x).property
  have he := LinearMap.congr_fun
    (map_homogeneousHistory_totalTransfer_of_admissible
      ℳ 𝓝 C D r σ hr hσ F hleft hright s hs p) x
  simp only [LinearMap.comp_apply, LinearMap.restrict_apply, Submodule.subtype_apply] at he
  rw [← he]
  constructor
  · intro hz
    have hzero : (r b).restrict (hr b (s b)) ⟨_, hmem⟩ = 0 := Subtype.ext hz
    exact congrArg Subtype.val (hinj (hzero.trans (map_zero _).symm))
  · intro hz
    simp [hz]

end TauCeti.GradedCorrespondence
