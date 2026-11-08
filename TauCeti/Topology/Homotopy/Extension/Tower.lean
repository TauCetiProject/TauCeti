/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Coherent
public import TauCeti.Topology.Homotopy.Extension.HomotopyEquivRel

/-!
# Homotopy equivalences of towers of cofibrations

Let `X = ⋃ₙ Xₙ` and `Y = ⋃ₙ Yₙ` be increasing unions carrying the final topology, in which each
stage `Xₙ` has the homotopy extension property in the next stage `Xₙ₊₁`, and likewise for `Y`.
Let `f : X → Y` be a map carrying each `Xₙ` into `Yₙ` whose restrictions `fₙ : Xₙ → Yₙ` are
homotopy equivalences. Then `f` is a homotopy equivalence, with a homotopy inverse carrying each
`Yₙ` into `Xₙ` (`TauCeti.exists_homotopyEquiv_of_cofibrationTower`).

This is how a homotopy equivalence is passed from the finite stages of an exhaustion to the whole
space: for instance from the regular sublevels `M_{aₙ}` of a proper Morse function and the CW
complexes modelling them to the manifold `M` and the CW complex built from the whole tower. No
inverses or homotopies at the stages are required as input, only that each `fₙ` is a homotopy
equivalence; and the maps `fₙ` commute strictly with the inclusions, being restrictions of a single
map `f`.

## Proof

The proof extends inverses stage by stage and uses no mapping telescopes. A homotopy inverse of
`f₀` starts a sequence of left homotopy inverses `gₙ` of the `fₙ`, with homotopies
`Hₙ : gₙ ∘ fₙ ≃ id`. At each step,
`TauCeti.HasHomotopyExtensionProperty.exists_inverse_extending_homotopy` extends `gₙ` and `Hₙ`
from the cofibrations `Yₙ ⊆ Yₙ₊₁` and `Xₙ ⊆ Xₙ₊₁` to a homotopy inverse `gₙ₊₁` of `fₙ₊₁` and a
homotopy `Hₙ₊₁ : gₙ₊₁ ∘ fₙ₊₁ ≃ id` extending `Hₙ`. These strictly compatible maps
and homotopies glue to a left homotopy inverse `g` of `f` with a homotopy `H : g ∘ f ≃ id`
carrying each `[0, 1] × Xₙ` into `Xₙ` (`TauCeti.exists_leftInverse_of_cofibrationTower`). The
homotopy is continuous because `[0, 1]` is locally compact, so that `[0, 1] × X` carries the final
topology of the `[0, 1] × Xₙ` (`Topology.IsCoherentWith.univ_prod`).

The restrictions `gₙ` of `g` are homotopy equivalences again, so the same construction gives a
left homotopy inverse `f'` of `g`. Then `f ≃ f' ∘ g ∘ f ≃ f'`, so `f ∘ g ≃ f' ∘ g ≃ id`, and `g` is
a two-sided homotopy inverse of `f`.

## Main results

* `TauCeti.exists_leftInverse_of_cofibrationTower`: a map of towers of cofibrations which is a
  homotopy equivalence at every stage has a left homotopy inverse restricting to homotopy inverses
  at every stage, with a left homotopy preserving every stage.
* `TauCeti.exists_homotopyEquiv_of_cofibrationTower`: **a map of towers of cofibrations which is
  a homotopy equivalence at every stage is a homotopy equivalence of the unions.**

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Proposition 0.19.
* T. tom Dieck, *Algebraic Topology*, EMS Textbooks in Mathematics, 2008, Chapter 5, for
  homotopy equivalences of pairs of cofibrations and their colimits.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousMap Set Topology unitInterval

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- A left homotopy inverse of `φ` together with a homotopy from its composite with `φ` to the
identity. -/
private abbrev LeftHomotopyInverse {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    (φ : C(A, B)) :=
  Σ g : C(B, A), (g.comp φ).Homotopy (ContinuousMap.id A)

/-- The homeomorphism between the points of the subtype `s₁` lying in `s₀ ⊆ s₁` and `s₀`. -/
private def preimageValHomeomorph {s₀ s₁ : Set X} (h : s₀ ⊆ s₁) :
    ((↑) ⁻¹' s₀ : Set s₁) ≃ₜ s₀ where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨⟨x, h x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- **One step of the tower.** Let `s₀ ⊆ s₁` and `t₀ ⊆ t₁` be cofibrations, and let
`e₁ : s₁ ≃ₕ t₁` restrict to a homotopy equivalence `e₀ : s₀ ≃ₕ t₀`. A left homotopy inverse of
`e₀`, with its homotopy, extends to a left homotopy inverse of `e₁` with a homotopy extending the
given one. -/
private theorem exists_leftHomotopyInverse_extend {s₀ s₁ : Set X} {t₀ t₁ : Set Y}
    (hs : s₀ ⊆ s₁) (ht : t₀ ⊆ t₁) (hsH : HasHomotopyExtensionProperty ((↑) ⁻¹' s₀ : Set s₁))
    (htH : HasHomotopyExtensionProperty ((↑) ⁻¹' t₀ : Set t₁)) (e₀ : s₀ ≃ₕ t₀) (e₁ : s₁ ≃ₕ t₁)
    (he : ∀ x : s₀, (e₀ x : Y) = e₁ ⟨x, hs x.2⟩) (d : LeftHomotopyInverse e₀.toFun) :
    ∃ d' : LeftHomotopyInverse e₁.toFun,
      (∀ (y : t₁) (hy : (y : Y) ∈ t₀), (d'.1 y : X) = d.1 ⟨y, hy⟩) ∧
        ∀ (τ : I) (x : s₁) (hx : (x : X) ∈ s₀), (d'.2 (τ, x) : X) = d.2 (τ, ⟨x, hx⟩) := by
  let iA := preimageValHomeomorph hs
  let iB := preimageValHomeomorph ht
  -- Transport `e₀`, `d.1` and `d.2` to the subsets `s₀ ⊆ s₁` and `t₀ ⊆ t₁`.
  let h₀ : ((↑) ⁻¹' s₀ : Set s₁) ≃ₕ ((↑) ⁻¹' t₀ : Set t₁) :=
    (iA.toHomotopyEquiv.trans e₀).trans iB.symm.toHomotopyEquiv
  have hh₀ (a : ((↑) ⁻¹' s₀ : Set s₁)) : (h₀ a : t₁) = e₁ a := Subtype.ext (he (iA a))
  let g₀ : C(((↑) ⁻¹' t₀ : Set t₁), ((↑) ⁻¹' s₀ : Set s₁)) :=
    (iA.symm : C(s₀, _)).comp (d.1.comp (iB : C(_, t₀)))
  let H₀ : (g₀.comp h₀.toFun).Homotopy (ContinuousMap.id _) :=
    { toFun := fun p => iA.symm (d.2 (p.1, iA p.2))
      continuous_toFun := by fun_prop
      map_zero_left := fun a => by rw [d.2.apply_zero]; rfl
      map_one_left := fun a => by simp }
  obtain ⟨g, H, hg, hH, -⟩ := hsH.exists_inverse_extending_homotopy htH e₁ h₀ hh₀ g₀ H₀
  exact ⟨⟨g, H⟩, fun y hy => congrArg Subtype.val (hg ⟨y, hy⟩),
    fun τ x hx => congrArg Subtype.val (hH τ ⟨x, hx⟩)⟩

variable {s : ℕ → Set X} {t : ℕ → Set Y}

/-- **A left homotopy inverse of a map of towers of cofibrations.** Let `X` and `Y` carry the
final topologies of increasing unions of stages `s n` and `t n`, each stage having the homotopy
extension property in the next. Let `f : X → Y` restrict to homotopy equivalences
`e n : s n ≃ₕ t n`. Then `f` has a left homotopy inverse `g`, restricting to homotopy inverses
`e' n : t n ≃ₕ s n` of the `e n`, with a homotopy `g ∘ f ≃ id` carrying each stage `s n` into
itself at all times. -/
theorem exists_leftInverse_of_cofibrationTower (hs : Monotone s)
    (ht : Monotone t) (hsX : IsCoherentWith (range s)) (hsU : ⋃ n, s n = univ)
    (htY : IsCoherentWith (range t)) (htU : ⋃ n, t n = univ)
    (hsH : ∀ n, HasHomotopyExtensionProperty ((↑) ⁻¹' s n : Set (s (n + 1))))
    (htH : ∀ n, HasHomotopyExtensionProperty ((↑) ⁻¹' t n : Set (t (n + 1))))
    (f : C(X, Y)) (e : ∀ n, s n ≃ₕ t n) (he : ∀ n (x : s n), (e n x : Y) = f x) :
    ∃ (g : C(Y, X)) (H : (g.comp f).Homotopy (ContinuousMap.id X)) (e' : ∀ n, t n ≃ₕ s n),
      (∀ n (y : t n), (e' n y : X) = g y) ∧
        ∀ n (τ : I), MapsTo (fun x => H (τ, x)) (s n) (s n) := by
  -- Build compatible left homotopy inverses of the `e n`, stage by stage.
  choose step hstep₁ hstep₂ using fun n => exists_leftHomotopyInverse_extend
    (hs n.le_succ) (ht n.le_succ) (hsH n) (htH n) (e n) (e (n + 1))
    fun x => (he n x).trans (he (n + 1) ⟨x, hs n.le_succ x.2⟩).symm
  let d (n : ℕ) : LeftHomotopyInverse (e n).toFun :=
    Nat.rec (motive := fun n => LeftHomotopyInverse (e n).toFun)
      ⟨(e 0).invFun, (e 0).left_inv.some⟩ step n
  have hd₁ {n m : ℕ} (hnm : n ≤ m) (y : Y) (hy : y ∈ t n) :
      ((d m).1 ⟨y, ht hnm hy⟩ : X) = (d n).1 ⟨y, hy⟩ := by
    induction m, hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih => exact (hstep₁ m (d m) ⟨y, _⟩ (ht hnm hy)).trans ih
  have hd₂ {n m : ℕ} (hnm : n ≤ m) (τ : I) (x : X) (hx : x ∈ s n) :
      ((d m).2 (τ, ⟨x, hs hnm hx⟩) : X) = (d n).2 (τ, ⟨x, hx⟩) := by
    induction m, hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih => exact (hstep₂ m (d m) τ ⟨x, _⟩ (hs hnm hx)).trans ih
  -- Glue the stages together.
  have hsN (x : X) : ∃ n, x ∈ s n := mem_iUnion.1 (hsU ▸ mem_univ x)
  have htN (y : Y) : ∃ n, y ∈ t n := mem_iUnion.1 (htU ▸ mem_univ y)
  choose N hN using htN
  choose N' hN' using hsN
  let gf (y : Y) : X := (d (N y)).1 ⟨y, hN y⟩
  have hgf (n : ℕ) (y : Y) (hy : y ∈ t n) : gf y = (d n).1 ⟨y, hy⟩ :=
    (hd₁ (le_max_left (N y) n) y (hN y)).symm.trans (hd₁ (le_max_right (N y) n) y hy)
  let Hf (p : I × X) : X := (d (N' p.2)).2 (p.1, ⟨p.2, hN' p.2⟩)
  have hHf (n : ℕ) (τ : I) (x : X) (hx : x ∈ s n) : Hf (τ, x) = (d n).2 (τ, ⟨x, hx⟩) :=
    (hd₂ (le_max_left (N' x) n) τ x (hN' x)).symm.trans (hd₂ (le_max_right (N' x) n) τ x hx)
  have hgc : Continuous gf := htY.continuous_iff.2 <| by
    rintro _ ⟨n, rfl⟩
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp (d n).1.continuous).congr fun y => (hgf n y y.2).symm
  have hHc : Continuous Hf := (hsX.univ_prod ((sUnion_range s).trans hsU)).continuous_iff.2 <| by
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous fun p : (univ ×ˢ s n : Set (I × X)) =>
        ((d n).2 (p.1.1, ⟨p.1.2, p.2.2⟩) : X) :=
      continuous_subtype_val.comp ((d n).2.continuous.comp
        ((continuous_fst.comp continuous_subtype_val).prodMk
          ((continuous_snd.comp continuous_subtype_val).subtype_mk fun p => p.2.2)))
    exact hc.congr fun p => (hHf n p.1.1 p.1.2 p.2.2).symm
  let g : C(Y, X) := ⟨gf, hgc⟩
  have hgfx (n : ℕ) (x : s n) : g (f x) = (d n).1 (e n x) := by
    rw [← he n x]
    exact hgf n _ (e n x).2
  let H : (g.comp f).Homotopy (ContinuousMap.id X) :=
    { toFun := Hf
      continuous_toFun := hHc
      map_zero_left := fun x => by
        rw [hHf _ 0 x (hN' x), (d _).2.apply_zero]
        exact (hgfx _ ⟨x, hN' x⟩).symm
      map_one_left := fun x => by
        rw [hHf _ 1 x (hN' x), (d _).2.apply_one]
        rfl }
  refine ⟨g, H, fun n => ⟨(d n).1, (e n).toFun,
    (e n).toFun_comp_homotopic_id_of_comp_toFun_homotopic_id ⟨(d n).2⟩, ⟨(d n).2⟩⟩,
    fun n y => (hgf n y y.2).symm, fun n τ x hx => ?_⟩
  change Hf (τ, x) ∈ s n
  rw [hHf n τ x hx]
  exact ((d n).2 (τ, ⟨x, hx⟩)).2

/-- **Homotopy equivalences of towers of cofibrations.** Let `X` and `Y` carry the final
topologies of increasing unions of stages `s n` and `t n`, each stage having the homotopy
extension property in the next. If `f : X → Y` restricts to homotopy equivalences
`e n : s n ≃ₕ t n`, then `f` is a homotopy equivalence, with a homotopy inverse carrying each
stage `t n` into `s n`. -/
theorem exists_homotopyEquiv_of_cofibrationTower (hs : Monotone s)
    (ht : Monotone t) (hsX : IsCoherentWith (range s)) (hsU : ⋃ n, s n = univ)
    (htY : IsCoherentWith (range t)) (htU : ⋃ n, t n = univ)
    (hsH : ∀ n, HasHomotopyExtensionProperty ((↑) ⁻¹' s n : Set (s (n + 1))))
    (htH : ∀ n, HasHomotopyExtensionProperty ((↑) ⁻¹' t n : Set (t (n + 1))))
    (f : C(X, Y)) (e : ∀ n, s n ≃ₕ t n) (he : ∀ n (x : s n), (e n x : Y) = f x) :
    ∃ E : X ≃ₕ Y, E.toFun = f ∧ ∀ n, MapsTo E.symm (t n) (s n) := by
  obtain ⟨g, H, e', he', -⟩ :=
    exists_leftInverse_of_cofibrationTower hs ht hsX hsU htY htU hsH htH f e he
  -- The restrictions of `g` are homotopy equivalences, so `g` has a left homotopy inverse `f'`.
  obtain ⟨f', H', -, -, -⟩ :=
    exists_leftInverse_of_cofibrationTower ht hs htY htU hsX hsU htH hsH g e' he'
  -- Then `f ≃ f' ∘ g ∘ f ≃ f'`, so `f ∘ g ≃ f' ∘ g ≃ id`.
  have hff' : f.Homotopic f' := by
    have h₁ := (Homotopic.symm ⟨H'⟩).comp (Homotopic.refl f)
    have h₂ := (Homotopic.refl f').comp (⟨H⟩ : (g.comp f).Homotopic (ContinuousMap.id X))
    rw [ContinuousMap.id_comp, ContinuousMap.comp_assoc] at h₁
    rw [ContinuousMap.comp_id] at h₂
    exact h₁.trans h₂
  refine ⟨⟨f, g, ⟨H⟩, (hff'.comp (Homotopic.refl g)).trans ⟨H'⟩⟩, rfl, fun n y hy => ?_⟩
  change g y ∈ s n
  rw [← he' n ⟨y, hy⟩]
  exact (e' n ⟨y, hy⟩).2

end TauCeti
