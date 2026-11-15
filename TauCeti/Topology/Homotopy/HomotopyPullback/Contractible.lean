/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyEquiv
public import TauCeti.Topology.Homotopy.HomotopyPullback.Cartesian

/-!
# Homotopy pullbacks and homotopy-cartesian squares with contractible spaces

This file develops the two contractibility reductions for homotopy pullbacks and
homotopy-cartesian squares:

1. **Contractible base** (`TauCeti.HomotopyPullback.prodFiberHomotopyEquivOfContraction`,
   `TauCeti.HomotopyPullback.prodHomotopyEquiv`): when the common target `B` of `f : C(A, B)` and
   `g : C(C, B)` contracts to `b₀ : B` via `K : (.id B).Homotopy (.const B b₀)`, the corner
   projection `(fst f g).prodMk (snd f g) : HomotopyPullback f g → A × C` is part of an explicit
   fibre homotopy equivalence over `A × C`, with homotopy inverse sending `(a, c)` to
   `(a, c, (K.evalAt (f a)).trans (K.evalAt (g c)).symm)`. In particular, when
   `[ContractibleSpace B]`, `HomotopyPullback f g ≃ₕ A × C` via `(fst f g).prodMk (snd f g)`, a
   square over `B` is homotopy-cartesian if and only if `α.prodMk p' : E' → E × B'` is a weak
   homotopy equivalence, and `HomotopyPullback f g` is contractible whenever `A`, `B`, and `C` are.

2. **Contractible bottom-left corner**
   (`TauCeti.HomotopyPullback.mappingPathFiberHomotopyEquivOfContraction`,
   `ContinuousMap.Homotopy.isHomotopyCartesian_iff_of_contraction`,
   `ContinuousMap.Homotopy.isHomotopyCartesian_iff_toMappingPathFiber`,
   `TauCeti.isHomotopyCartesian_iff_of_contraction`,
   `TauCeti.isHomotopyCartesian_iff_toMappingPathFiber`): in a homotopy-commutative square
   `H : (p.comp α).Homotopy (h.comp p')` whose bottom-left space `B'` contracts to `b' : B'` via
   `K : (.id B').Homotopy (.const B' b')`, homotopy invariance of `HomotopyPullback p h` in its
   right leg together with `HomotopyPullback.constRightProdHomeomorph` and projection away from `B'`
   gives `HomotopyPullback p h ≃ₕ MappingPathFiber p (h b')`. Composing with
   `HomotopyPullback.lift α p' H` identifies homotopy-cartesianness of the square with weak
   homotopy equivalence of the comparison map `E' → MappingPathFiber p (h b')` sending `e'` to
   `(α e', (H.evalAt e').trans ((K.evalAt (p' e')).map h.continuous))` (or simply
   `(α e', (K.evalAt (p' e')).map h.continuous)` when the square commutes strictly).

   Specializing `B' = Unit` recovers the strict-fibre comparison `MappingPathFiber.ofFiber p b`
   (`TauCeti.isHomotopyCartesian_fiber_iff_ofFiber`), while assuming `[ContractibleSpace E']` as
   well shows that a square with contractible left-hand corners is homotopy-cartesian if and only if
   `MappingPathFiber p (h b')` is weakly contractible
   (`ContinuousMap.Homotopy.isHomotopyCartesian_iff_const_mappingPathFiber`).

## Main declarations

* `ContinuousMap.idContraction`: an explicit contraction `(.id X).Homotopy (.const X x₀)` of a
  `ContractibleSpace` to any chosen basepoint `x₀ : X`.
* `ContinuousMap.HomotopyEquiv.prodOfContraction`: `X × Y ≃ₕ X` via `ContinuousMap.fst` from an
  explicit contraction of `Y`.
* `TauCeti.HomotopyPullback.prodFiberHomotopyEquivOfContraction`,
  `TauCeti.HomotopyPullback.prodHomotopyEquivOfContraction`,
  `TauCeti.HomotopyPullback.prodFiberHomotopyEquiv`, and
  `TauCeti.HomotopyPullback.prodHomotopyEquiv`: `HomotopyPullback f g ≃ₕ A × C` over a
  contracted or `[ContractibleSpace]` base `B`.
* `ContinuousMap.Homotopy.isHomotopyCartesian_iff_prodMk` and
  `TauCeti.isHomotopyCartesian_iff_prodMk`: squares over a contractible base `B`.
* `TauCeti.HomotopyPullback.mappingPathFiberHomotopyEquivOfContraction` and
  `TauCeti.HomotopyPullback.mappingPathFiberHomotopyEquiv`:
  `HomotopyPullback p h ≃ₕ MappingPathFiber p (h b')` when `B'` contracts to `b'`.
* `ContinuousMap.Homotopy.toMappingPathFiberOfContraction`,
  `ContinuousMap.Homotopy.toMappingPathFiber`,
  `ContinuousMap.Homotopy.isHomotopyCartesian_iff_of_contraction`, and
  `ContinuousMap.Homotopy.isHomotopyCartesian_iff_toMappingPathFiber`: contractible-corner criteria
  for homotopy-commutative squares, together with strict-square (`TauCeti`) and `TopCat` (`CommSq`)
  specializations.
* `TauCeti.isHomotopyCartesian_fiber_iff_ofFiber`: specialization to a point inclusion `Unit → B`.
* `ContinuousMap.Homotopy.isHomotopyCartesian_iff_const_mappingPathFiber`: criterion when both `E'`
  and `B'` are contractible.

## References

* M. Mather, *Pull-backs in homotopy theory*, Canadian Journal of Mathematics 28 (1976), 225–263.
* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Mathematics 341, Springer, 1973, §1.
* A. Hatcher, *Algebraic Topology*, Proposition 4.65.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapters I.7 and IV.8.
-/

public section

open CategoryTheory unitInterval
open scoped ContinuousMap

universe u v w u' v'

/-! ### Explicit contractions and projection equivalences -/

namespace ContinuousMap

/-- Any contractible space `X` admits a homotopy from `ContinuousMap.id X` to the constant map at an
arbitrary chosen point `x₀ : X`, obtained by concatenating a nullhomotopy of `id` with a path to
`x₀`. -/
noncomputable def idContraction {X : Type u} [TopologicalSpace X] [ContractibleSpace X]
    (x₀ : X) : (ContinuousMap.id X).Homotopy (.const X x₀) :=
  let x₁ := (id_nullhomotopic X).choose
  let H₁ : (ContinuousMap.id X).Homotopy (.const X x₁) := (id_nullhomotopic X).choose_spec.some
  let γ : Path x₁ x₀ := PathConnectedSpace.somePath x₁ x₀
  let H₂ : (ContinuousMap.const X x₁).Homotopy (.const X x₀) :=
    { toFun q := γ q.1
      continuous_toFun := γ.continuous.comp continuous_fst
      map_zero_left _ := γ.source
      map_one_left _ := γ.target }
  H₁.trans H₂

/-- Given an explicit contraction `K : (.id Y).Homotopy (.const Y y₀)`, the projection
`X × Y → X` is a homotopy equivalence with homotopy inverse `x ↦ (x, y₀)`. -/
def HomotopyEquiv.prodOfContraction (X : Type u) [TopologicalSpace X]
    {Y : Type v} [TopologicalSpace Y] (y₀ : Y)
    (K : (ContinuousMap.id Y).Homotopy (.const Y y₀)) :
    (X × Y) ≃ₕ X where
  toFun := fst
  invFun := (ContinuousMap.id X).prodMk (const X y₀)
  left_inv := Homotopic.symm ⟨{
    toFun q := (q.2.1, K (q.1, q.2.2))
    continuous_toFun := by fun_prop
    map_zero_left _ := by simp
    map_one_left _ := by simp }⟩
  right_inv := Homotopic.refl _

theorem HomotopyEquiv.prodOfContraction_toFun (X : Type u) [TopologicalSpace X]
    {Y : Type v} [TopologicalSpace Y] (y₀ : Y)
    (K : (ContinuousMap.id Y).Homotopy (.const Y y₀)) :
    (HomotopyEquiv.prodOfContraction X y₀ K).toFun = fst :=
  (rfl)

@[simp]
theorem HomotopyEquiv.coe_prodOfContraction (X : Type u) [TopologicalSpace X]
    {Y : Type v} [TopologicalSpace Y] (y₀ : Y)
    (K : (ContinuousMap.id Y).Homotopy (.const Y y₀)) :
    ⇑(HomotopyEquiv.prodOfContraction X y₀ K) = Prod.fst :=
  (rfl)

@[simp]
theorem HomotopyEquiv.prodOfContraction_symm_apply (X : Type u) [TopologicalSpace X]
    {Y : Type v} [TopologicalSpace Y] (y₀ : Y)
    (K : (ContinuousMap.id Y).Homotopy (.const Y y₀)) (x : X) :
    (HomotopyEquiv.prodOfContraction X y₀ K).symm x = (x, y₀) :=
  (rfl)

end ContinuousMap

/-! ### Homotopy pullbacks over a contracted or contractible base -/

namespace TauCeti.HomotopyPullback

section ContractibleBase

variable {A : Type u} {B : Type v} {C : Type w}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]

/-- Section `A × C → HomotopyPullback f g` associated to a contraction
`K : (.id B).Homotopy (.const B b₀)`, joining `f a` to `g c` through `b₀` along
`(K.evalAt (f a)).trans (K.evalAt (g c)).symm`. -/
noncomputable def sectionOfContraction (f : C(A, B)) (g : C(C, B)) {b₀ : B}
    (K : (ContinuousMap.id B).Homotopy (.const B b₀)) :
    C(A × C, HomotopyPullback f g) where
  toFun x := ⟨(x.1, x.2,
    ((K.evalAt (f x.1)).trans (K.evalAt (g x.2)).symm).toContinuousMap),
    Path.source _, Path.target _⟩
  continuous_toFun := by
    refine (continuous_fst.prodMk <| continuous_snd.prodMk ?_).subtype_mk _
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact Path.trans_continuous_family
      (fun x : A × C ↦ K.evalAt (f x.1))
      (K.continuous.comp (continuous_snd.prodMk
        (f.continuous.comp (continuous_fst.comp continuous_fst))))
      (fun x : A × C ↦ (K.evalAt (g x.2)).symm)
      (K.continuous.comp ((continuous_symm.comp continuous_snd).prodMk
        (g.continuous.comp (continuous_snd.comp continuous_fst))))

@[simp]
theorem sectionOfContraction_val (f : C(A, B)) (g : C(C, B)) {b₀ : B}
    (K : (ContinuousMap.id B).Homotopy (.const B b₀)) (x : A × C) :
    (sectionOfContraction f g K x).val =
      (x.1, x.2, ((K.evalAt (f x.1)).trans (K.evalAt (g x.2)).symm).toContinuousMap) :=
  (rfl)

theorem fst_sectionOfContraction (f : C(A, B)) (g : C(C, B)) {b₀ : B}
    (K : (ContinuousMap.id B).Homotopy (.const B b₀)) (x : A × C) :
    fst f g (sectionOfContraction f g K x) = x.1 := by
  simp

theorem snd_sectionOfContraction (f : C(A, B)) (g : C(C, B)) {b₀ : B}
    (K : (ContinuousMap.id B).Homotopy (.const B b₀)) (x : A × C) :
    snd f g (sectionOfContraction f g K x) = x.2 := by
  simp

theorem pathMap_sectionOfContraction_apply (f : C(A, B)) (g : C(C, B)) {b₀ : B}
    (K : (ContinuousMap.id B).Homotopy (.const B b₀)) (x : A × C) (t : I) :
    pathMap f g (sectionOfContraction f g K x) t =
      ((K.evalAt (f x.1)).trans (K.evalAt (g x.2)).symm) t := by
  simp
  rfl

@[simp]
theorem prodMk_comp_sectionOfContraction (f : C(A, B)) (g : C(C, B)) {b₀ : B}
    (K : (ContinuousMap.id B).Homotopy (.const B b₀)) :
    ((fst f g).prodMk (snd f g)).comp (sectionOfContraction f g K) = .id (A × C) := by
  ext ⟨_, _⟩ : 1
  simp

private theorem _root_.path_trans_apply_congr {X : Type*} [TopologicalSpace X]
    {a b c a' b' c' : X} (γ₁ : Path a b) (γ₂ : Path b c)
    (δ₁ : Path a' b') (δ₂ : Path b' c')
    (h₁ : ∀ u, γ₁ u = δ₁ u) (h₂ : ∀ u, γ₂ u = δ₂ u) (t : I) :
    (γ₁.trans γ₂) t = (δ₁.trans δ₂) t := by
  refine (Path.trans_apply γ₁ γ₂ t).trans (Eq.trans ?_ (Path.trans_apply δ₁ δ₂ t).symm)
  split_ifs
  · exact h₁ _
  · exact h₂ _

private def mkPathEndo {f : C(A, B)} {g : C(C, B)}
    (γ : ∀ p : HomotopyPullback f g, Path (f p.val.1) (g p.val.2.1))
    (hγ : Continuous ↿γ) :
    C(HomotopyPullback f g, HomotopyPullback f g) where
  toFun p := ⟨(p.val.1, p.val.2.1, (γ p).toContinuousMap), Path.source _, Path.target _⟩
  continuous_toFun :=
    (continuous_subtype_val.fst.prodMk <|
      continuous_subtype_val.snd.fst.prodMk
        (ContinuousMap.continuous_of_continuous_uncurry _ hγ)).subtype_mk _

private def homotopyWithOfPathFamily {f : C(A, B)} {g : C(C, B)}
    {φ₀ φ₁ : C(HomotopyPullback f g, HomotopyPullback f g)}
    (Γ : ∀ q : I × HomotopyPullback f g, Path (f q.2.val.1) (g q.2.val.2.1))
    (hΓ : Continuous ↿Γ)
    (h₀ : ∀ p, φ₀ p = ⟨(p.val.1, p.val.2.1, (Γ (0, p)).toContinuousMap),
      Path.source _, Path.target _⟩)
    (h₁ : ∀ p, φ₁ p = ⟨(p.val.1, p.val.2.1, (Γ (1, p)).toContinuousMap),
      Path.source _, Path.target _⟩) :
    ContinuousMap.HomotopyWith φ₀ φ₁
      (fun φ ↦ ((fst f g).prodMk (snd f g)).comp φ = (fst f g).prodMk (snd f g)) where
  toFun q := ⟨(q.2.val.1, q.2.val.2.1, (Γ q).toContinuousMap), Path.source _, Path.target _⟩
  continuous_toFun :=
    ((continuous_subtype_val.fst.comp continuous_snd).prodMk <|
      (continuous_subtype_val.snd.fst.comp continuous_snd).prodMk
        (ContinuousMap.continuous_of_continuous_uncurry _ hΓ)).subtype_mk _
  map_zero_left p := (h₀ p).symm
  map_one_left p := (h₁ p).symm
  prop' _ := by ext : 1; simp

private theorem sectionOfContraction_comp_prodMk_homotopicWith
    (f : C(A, B)) (g : C(C, B)) {b₀ : B}
    (K : (ContinuousMap.id B).Homotopy (.const B b₀)) :
    ((sectionOfContraction f g K).comp ((fst f g).prodMk (snd f g))).HomotopicWith
      (.id (HomotopyPullback f g))
      (fun φ ↦ ((fst f g).prodMk (snd f g)).comp φ = (fst f g).prodMk (snd f g)) := by
  have hpath : Continuous ↿fun p : HomotopyPullback f g ↦ path p := by
    have h : (↿fun p : HomotopyPullback f g ↦ path p) =
        fun z : HomotopyPullback f g × I ↦ z.1.val.2.2 z.2 := by
      ext ⟨p, t⟩
      change path p t = p.val.2.2 t
      simp
    rw [h]
    exact (continuous_subtype_val.snd.snd.comp continuous_fst).eval continuous_snd
  have hrefl_g : Continuous ↿fun p : HomotopyPullback f g ↦ Path.refl (g p.val.2.1) :=
    g.continuous.comp (continuous_subtype_val.snd.fst.comp continuous_fst)
  have hrefl_f : Continuous ↿fun p : HomotopyPullback f g ↦ Path.refl (f p.val.1) :=
    f.continuous.comp (continuous_subtype_val.fst.comp continuous_fst)
  have htr : Continuous ↿fun p : HomotopyPullback f g ↦
      (path p).trans (Path.refl (g p.val.2.1)) :=
    Path.trans_continuous_family _ hpath _ hrefl_g
  have hltr : Continuous ↿fun p : HomotopyPullback f g ↦
      (Path.refl (f p.val.1)).trans ((path p).trans (Path.refl (g p.val.2.1))) :=
    Path.trans_continuous_family _ hrefl_f _ htr
  have hKf : Continuous ↿fun p : HomotopyPullback f g ↦ K.evalAt (f p.val.1) :=
    K.continuous.comp (continuous_snd.prodMk
      (f.continuous.comp (continuous_subtype_val.fst.comp continuous_fst)))
  have hKg_symm : Continuous ↿fun p : HomotopyPullback f g ↦ (K.evalAt (g p.val.2.1)).symm :=
    K.continuous.comp ((continuous_symm.comp continuous_snd).prodMk
      (g.continuous.comp (continuous_subtype_val.snd.fst.comp continuous_fst)))
  have hmid : Continuous ↿fun p : HomotopyPullback f g ↦
      (K.evalAt (f p.val.1)).trans ((Path.refl b₀).trans (K.evalAt (g p.val.2.1)).symm) :=
    Path.trans_continuous_family _ hKf _
      (Path.trans_continuous_family _ continuous_const _ hKg_symm)
  have hpath' : Continuous ↿fun q : I × HomotopyPullback f g ↦ path q.2 :=
    hpath.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have htr' : Continuous ↿fun q : I × HomotopyPullback f g ↦
      (path q.2).trans (Path.refl (g q.2.val.2.1)) :=
    htr.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hKf' : Continuous ↿fun q : I × HomotopyPullback f g ↦ K.evalAt (f q.2.val.1) :=
    hKf.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hKg_symm' : Continuous ↿fun q : I × HomotopyPullback f g ↦
      (K.evalAt (g q.2.val.2.1)).symm :=
    hKg_symm.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  let ψ₁ := mkPathEndo (fun p : HomotopyPullback f g ↦
    (path p).trans (Path.refl (g p.val.2.1))) htr
  let ψ₂ := mkPathEndo (fun p : HomotopyPullback f g ↦
    (Path.refl (f p.val.1)).trans ((path p).trans (Path.refl (g p.val.2.1)))) hltr
  let ψ₃ := mkPathEndo (fun p : HomotopyPullback f g ↦
    (K.evalAt (f p.val.1)).trans ((Path.refl b₀).trans (K.evalAt (g p.val.2.1)).symm)) hmid
  have H₀₁ : ContinuousMap.HomotopyWith ψ₁ (.id (HomotopyPullback f g))
      (fun φ ↦ ((fst f g).prodMk (snd f g)).comp φ = (fst f g).prodMk (snd f g)) := by
    refine homotopyWithOfPathFamily
      (fun q ↦ (Path.delayReflLeft q.1 (path q.2).symm).symm)
      (Path.symm_continuous_family _
        (Path.delayReflLeft_continuous_family _
          (Path.symm_continuous_family _ hpath') ContinuousMap.fst))
      (fun p ↦ ?_) (fun p ↦ ?_)
    · refine Subtype.ext <| Prod.ext rfl <| Prod.ext rfl <| ContinuousMap.ext fun t ↦ ?_
      change ((path p).trans (Path.refl (g p.val.2.1))) t =
        (Path.delayReflLeft 0 (path p).symm).symm t
      rw [Path.delayReflLeft_zero, Path.trans_symm]
      simp
    · refine Subtype.ext <| Prod.ext rfl <| Prod.ext rfl <| ContinuousMap.ext fun t ↦ ?_
      change p.val.2.2 t = (Path.delayReflLeft 1 (path p).symm).symm t
      rw [Path.delayReflLeft_one, Path.symm_symm]
      simp
  have H₁₂ : ContinuousMap.HomotopyWith ψ₂ ψ₁
      (fun φ ↦ ((fst f g).prodMk (snd f g)).comp φ = (fst f g).prodMk (snd f g)) := by
    refine homotopyWithOfPathFamily
      (fun q ↦ Path.delayReflLeft q.1 ((path q.2).trans (Path.refl (g q.2.val.2.1))))
      (Path.delayReflLeft_continuous_family _ htr' ContinuousMap.fst)
      (fun p ↦ ?_) (fun p ↦ ?_)
    · refine Subtype.ext <| Prod.ext rfl <| Prod.ext rfl <| ContinuousMap.ext fun t ↦ ?_
      change ((Path.refl (f p.val.1)).trans ((path p).trans (Path.refl (g p.val.2.1)))) t =
        Path.delayReflLeft 0 ((path p).trans (Path.refl (g p.val.2.1))) t
      rw [Path.delayReflLeft_zero]
    · refine Subtype.ext <| Prod.ext rfl <| Prod.ext rfl <| ContinuousMap.ext fun t ↦ ?_
      change ((path p).trans (Path.refl (g p.val.2.1))) t =
        Path.delayReflLeft 1 ((path p).trans (Path.refl (g p.val.2.1))) t
      rw [Path.delayReflLeft_one]
  let α (s : I) (b : B) : Path b (K (s, b)) :=
    { toFun t := K (s * t, b)
      continuous_toFun := K.continuous.comp
        ((continuous_const.mul continuous_id).prodMk continuous_const)
      source' := by simp
      target' := by simp }
  let γ_s (s : I) (p : HomotopyPullback f g) : Path (K (s, f p.val.1)) (K (s, g p.val.2.1)) :=
    (path p).map (K.continuous.comp (continuous_const.prodMk continuous_id))
  have H₂₃ : ContinuousMap.HomotopyWith ψ₂ ψ₃
      (fun φ ↦ ((fst f g).prodMk (snd f g)).comp φ = (fst f g).prodMk (snd f g)) := by
    have hαf : Continuous ↿fun q : I × HomotopyPullback f g ↦ α q.1 (f q.2.val.1) :=
      K.continuous.comp
        (((continuous_fst.comp continuous_fst).mul continuous_snd).prodMk
          (f.continuous.comp (continuous_subtype_val.fst.comp
            (continuous_snd.comp continuous_fst))))
    have hαg : Continuous ↿fun q : I × HomotopyPullback f g ↦ α q.1 (g q.2.val.2.1) :=
      K.continuous.comp
        (((continuous_fst.comp continuous_fst).mul continuous_snd).prodMk
          (g.continuous.comp (continuous_subtype_val.snd.fst.comp
            (continuous_snd.comp continuous_fst))))
    have hγs : Continuous ↿fun q : I × HomotopyPullback f g ↦ γ_s q.1 q.2 :=
      K.continuous.comp ((continuous_fst.comp continuous_fst).prodMk hpath')
    refine homotopyWithOfPathFamily
      (fun q ↦ (α q.1 (f q.2.val.1)).trans ((γ_s q.1 q.2).trans (α q.1 (g q.2.val.2.1)).symm))
      (Path.trans_continuous_family _ hαf _
        (Path.trans_continuous_family _ hγs _ (Path.symm_continuous_family _ hαg)))
      (fun p ↦ ?_) (fun p ↦ ?_)
    · refine Subtype.ext <| Prod.ext rfl <| Prod.ext rfl <| ContinuousMap.ext fun t ↦ ?_
      change ((Path.refl (f p.val.1)).trans ((path p).trans (Path.refl (g p.val.2.1)))) t =
        ((α 0 (f p.val.1)).trans ((γ_s 0 p).trans (α 0 (g p.val.2.1)).symm)) t
      simp [α, γ_s, Path.trans_apply]
    · refine Subtype.ext <| Prod.ext rfl <| Prod.ext rfl <| ContinuousMap.ext fun t ↦ ?_
      change ((K.evalAt (f p.val.1)).trans
          ((Path.refl b₀).trans (K.evalAt (g p.val.2.1)).symm)) t =
        ((α 1 (f p.val.1)).trans ((γ_s 1 p).trans (α 1 (g p.val.2.1)).symm)) t
      exact path_trans_apply_congr (K.evalAt (f p.val.1))
        ((Path.refl b₀).trans (K.evalAt (g p.val.2.1)).symm)
        (α 1 (f p.val.1)) ((γ_s 1 p).trans (α 1 (g p.val.2.1)).symm)
        (fun _ ↦ by simp [α]; rfl)
        (fun u ↦ path_trans_apply_congr (Path.refl b₀) (K.evalAt (g p.val.2.1)).symm
          (γ_s 1 p) (α 1 (g p.val.2.1)).symm
          (fun _ ↦ by simp [γ_s])
          (fun _ ↦ by simp [α]; rfl) u) t
  have H₃₄ : ContinuousMap.HomotopyWith ψ₃
      ((sectionOfContraction f g K).comp ((fst f g).prodMk (snd f g)))
      (fun φ ↦ ((fst f g).prodMk (snd f g)).comp φ = (fst f g).prodMk (snd f g)) := by
    refine homotopyWithOfPathFamily
      (fun q ↦ (K.evalAt (f q.2.val.1)).trans
        (Path.delayReflLeft q.1 (K.evalAt (g q.2.val.2.1)).symm))
      (Path.trans_continuous_family _ hKf' _
        (Path.delayReflLeft_continuous_family _ hKg_symm' ContinuousMap.fst))
      (fun p ↦ ?_) (fun p ↦ ?_)
    · refine Subtype.ext <| Prod.ext rfl <| Prod.ext rfl <| ContinuousMap.ext fun t ↦ ?_
      let δ₀ : Path b₀ (g p.val.2.1) := (K.evalAt (g p.val.2.1)).symm
      exact congrArg (fun δ : Path b₀ (g p.val.2.1) ↦ ((K.evalAt (f p.val.1)).trans δ) t)
        (Path.delayReflLeft_zero δ₀).symm
    · refine Subtype.ext <| Prod.ext (by simp) <| Prod.ext (by simp) <| ContinuousMap.ext fun t ↦ ?_
      have hsec : ((sectionOfContraction f g K (fst f g p, snd f g p)).val.2.2) t =
          ((K.evalAt (f p.val.1)).trans (K.evalAt (g p.val.2.1)).symm) t :=
        path_trans_apply_congr _ _ _ _
          (fun u ↦ by change K (u, f (fst f g p)) = K (u, f p.val.1); simp)
          (fun u ↦ by change K (σ u, g (snd f g p)) = K (σ u, g p.val.2.1); simp) t
      refine hsec.trans ?_
      let δ₀ : Path b₀ (g p.val.2.1) := (K.evalAt (g p.val.2.1)).symm
      exact congrArg (fun δ : Path b₀ (g p.val.2.1) ↦ ((K.evalAt (f p.val.1)).trans δ) t)
        (Path.delayReflLeft_one δ₀).symm
  exact ⟨(H₀₁.symm.trans (H₁₂.symm.trans (H₂₃.trans H₃₄))).symm⟩

/-- **Homotopy pullback over a contracted base (fibrewise form).** Given an explicit contraction
`K : (.id B).Homotopy (.const B b₀)`, the projection
`(fst f g).prodMk (snd f g) : HomotopyPullback f g → A × C` is a fibre homotopy equivalence over
`A × C` with homotopy inverse `sectionOfContraction f g K`. -/
noncomputable def prodFiberHomotopyEquivOfContraction (f : C(A, B)) (g : C(C, B)) (b₀ : B)
    (K : (ContinuousMap.id B).Homotopy (.const B b₀)) :
    FiberHomotopyEquiv ((fst f g).prodMk (snd f g)) (.id (A × C)) where
  toFun := (fst f g).prodMk (snd f g)
  invFun := sectionOfContraction f g K
  comp_toFun := ContinuousMap.id_comp _
  comp_invFun := prodMk_comp_sectionOfContraction f g K
  left_inv := sectionOfContraction_comp_prodMk_homotopicWith f g K
  right_inv := ⟨{
    toHomotopy := (ContinuousMap.Homotopy.refl (.id (A × C))).cast
      (prodMk_comp_sectionOfContraction f g K).symm rfl
    prop' := fun _ ↦ ContinuousMap.id_comp _ }⟩

@[simp]
theorem prodFiberHomotopyEquivOfContraction_toFun (f : C(A, B)) (g : C(C, B)) (b₀ : B)
    (K : (ContinuousMap.id B).Homotopy (.const B b₀)) :
    (prodFiberHomotopyEquivOfContraction f g b₀ K).toFun = (fst f g).prodMk (snd f g) :=
  (rfl)

@[simp]
theorem prodFiberHomotopyEquivOfContraction_invFun (f : C(A, B)) (g : C(C, B)) (b₀ : B)
    (K : (ContinuousMap.id B).Homotopy (.const B b₀)) :
    (prodFiberHomotopyEquivOfContraction f g b₀ K).invFun = sectionOfContraction f g K :=
  (rfl)

/-- **Homotopy pullback over a contracted base.** Given an explicit contraction
`K : (.id B).Homotopy (.const B b₀)`, `HomotopyPullback f g` is homotopy equivalent to `A × C`
via `(fst f g).prodMk (snd f g)`. -/
noncomputable def prodHomotopyEquivOfContraction (f : C(A, B)) (g : C(C, B)) (b₀ : B)
    (K : (ContinuousMap.id B).Homotopy (.const B b₀)) :
    HomotopyPullback f g ≃ₕ A × C :=
  (prodFiberHomotopyEquivOfContraction f g b₀ K).toHomotopyEquiv

@[simp]
theorem prodHomotopyEquivOfContraction_toFun (f : C(A, B)) (g : C(C, B)) (b₀ : B)
    (K : (ContinuousMap.id B).Homotopy (.const B b₀)) :
    (prodHomotopyEquivOfContraction f g b₀ K).toFun = (fst f g).prodMk (snd f g) := by
  ext p : 1
  simp [prodHomotopyEquivOfContraction]

theorem prodHomotopyEquivOfContraction_apply (f : C(A, B)) (g : C(C, B)) (b₀ : B)
    (K : (ContinuousMap.id B).Homotopy (.const B b₀)) (p : HomotopyPullback f g) :
    prodHomotopyEquivOfContraction f g b₀ K p = (fst f g p, snd f g p) := by
  simp [prodHomotopyEquivOfContraction]

@[simp]
theorem prodHomotopyEquivOfContraction_symm_apply (f : C(A, B)) (g : C(C, B)) (b₀ : B)
    (K : (ContinuousMap.id B).Homotopy (.const B b₀)) (x : A × C) :
    (prodHomotopyEquivOfContraction f g b₀ K).symm x = sectionOfContraction f g K x := by
  simp [prodHomotopyEquivOfContraction]

/-- **Homotopy pullback over a contractible base (fibrewise form).** When `[ContractibleSpace B]`,
`(fst f g).prodMk (snd f g)` is part of a fibre homotopy equivalence over `A × C`. -/
noncomputable def prodFiberHomotopyEquiv [ContractibleSpace B] (f : C(A, B)) (g : C(C, B)) :
    FiberHomotopyEquiv ((fst f g).prodMk (snd f g)) (.id (A × C)) :=
  prodFiberHomotopyEquivOfContraction f g (id_nullhomotopic B).choose
    (id_nullhomotopic B).choose_spec.some

@[simp]
theorem prodFiberHomotopyEquiv_toFun [ContractibleSpace B] (f : C(A, B)) (g : C(C, B)) :
    (prodFiberHomotopyEquiv f g).toFun = (fst f g).prodMk (snd f g) :=
  (rfl)

/-- **Homotopy pullback over a contractible base.** When `[ContractibleSpace B]`,
`HomotopyPullback f g ≃ₕ A × C` via `(fst f g).prodMk (snd f g)`. -/
noncomputable def prodHomotopyEquiv [ContractibleSpace B] (f : C(A, B)) (g : C(C, B)) :
    HomotopyPullback f g ≃ₕ A × C :=
  (prodFiberHomotopyEquiv f g).toHomotopyEquiv

@[simp]
theorem prodHomotopyEquiv_toFun [ContractibleSpace B] (f : C(A, B)) (g : C(C, B)) :
    (prodHomotopyEquiv f g).toFun = (fst f g).prodMk (snd f g) := by
  ext p : 1
  simp [prodHomotopyEquiv]

theorem prodHomotopyEquiv_apply [ContractibleSpace B] (f : C(A, B)) (g : C(C, B))
    (p : HomotopyPullback f g) :
    prodHomotopyEquiv f g p = (fst f g p, snd f g p) := by
  simp [prodHomotopyEquiv]

/-- Over a contractible base `B`, the corner projection `(fst f g).prodMk (snd f g)` is a weak
homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_prodMk [ContractibleSpace B] (f : C(A, B)) (g : C(C, B)) :
    ((fst f g).prodMk (snd f g)).IsWeakHomotopyEquivalence :=
  prodHomotopyEquiv_toFun f g ▸ (prodHomotopyEquiv f g).isWeakHomotopyEquivalence

/-- The homotopy pullback of contractible spaces over a contractible base is contractible. -/
instance [ContractibleSpace A] [ContractibleSpace B] [ContractibleSpace C]
    (f : C(A, B)) (g : C(C, B)) :
    ContractibleSpace (HomotopyPullback f g) :=
  (prodHomotopyEquiv f g).contractibleSpace

end ContractibleBase

/-! ### Reduction of `HomotopyPullback p h` when the right corner contracts -/

section ContractibleCorner

variable {E : Type u} {B : Type v} {B' : Type v'}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace B']

/-- Postcomposing a contraction `K : (.id B').Homotopy (.const B' b')` with `h : C(B', B)` gives a
homotopy from `h` to `.const B' (h b')`. -/
def postcompContraction (h : C(B', B)) {b' : B'}
    (K : (ContinuousMap.id B').Homotopy (.const B' b')) :
    h.Homotopy (.const B' (h b')) where
  toFun q := h (K q)
  continuous_toFun := h.continuous.comp K.continuous
  map_zero_left x := congrArg h (K.apply_zero x)
  map_one_left x := congrArg h (K.apply_one x)

@[simp]
theorem postcompContraction_evalAt (h : C(B', B)) {b' : B'}
    (K : (ContinuousMap.id B').Homotopy (.const B' b')) (x : B') :
    (postcompContraction h K).evalAt x = (K.evalAt x).map h.continuous :=
  Path.ext rfl

/-- **Homotopy pullback along a map out of a contracted corner.** When `B'` contracts to `b' : B'`
via `K : (.id B').Homotopy (.const B' b')`, `HomotopyPullback p h` is homotopy equivalent to the
homotopy fibre `MappingPathFiber p (h b')`, sending `(e, x, γ)` to
`(e, γ.trans ((K.evalAt x).map h.continuous))`. -/
noncomputable def mappingPathFiberHomotopyEquivOfContraction
    (p : C(E, B)) (h : C(B', B)) (b' : B')
    (K : (ContinuousMap.id B').Homotopy (.const B' b')) :
    HomotopyPullback p h ≃ₕ MappingPathFiber p (h b') :=
  (((postcompContraction h K).homotopyPullbackRightHomotopyEquiv p).trans
    (constRightProdHomeomorph p (h b')).toHomotopyEquiv).trans
    (ContinuousMap.HomotopyEquiv.prodOfContraction (MappingPathFiber p (h b')) b' K)

@[simp]
theorem mappingPathFiberHomotopyEquivOfContraction_val_fst
    (p : C(E, B)) (h : C(B', B)) (b' : B')
    (K : (ContinuousMap.id B').Homotopy (.const B' b')) (q : HomotopyPullback p h) :
    (mappingPathFiberHomotopyEquivOfContraction p h b' K q).val.1 = fst p h q := by
  simp only [mappingPathFiberHomotopyEquivOfContraction, ContinuousMap.HomotopyEquiv.trans_apply,
    ContinuousMap.HomotopyEquiv.coe_prodOfContraction,
    ContinuousMap.Homotopy.homotopyPullbackRightHomotopyEquiv_apply]
  change ((constRightProdHomeomorph p (h b')
      (((postcompContraction h K).homotopyPullbackRightMap p) q)).1).val.1 = fst p h q
  rw [constRightProdHomeomorph_fst_val]
  exact ContinuousMap.Homotopy.fst_homotopyPullbackRightMap (postcompContraction h K) p q

@[simp]
theorem mappingPathFiberHomotopyEquivOfContraction_val_snd_apply
    (p : C(E, B)) (h : C(B', B)) (b' : B')
    (K : (ContinuousMap.id B').Homotopy (.const B' b')) (q : HomotopyPullback p h) (t : I) :
    (mappingPathFiberHomotopyEquivOfContraction p h b' K q).val.2 t =
      ((path q).trans ((K.evalAt q.val.2.1).map h.continuous)) t := by
  simp only [mappingPathFiberHomotopyEquivOfContraction, ContinuousMap.HomotopyEquiv.trans_apply,
    ContinuousMap.HomotopyEquiv.coe_prodOfContraction,
    ContinuousMap.Homotopy.homotopyPullbackRightHomotopyEquiv_apply]
  change ((constRightProdHomeomorph p (h b')
      (((postcompContraction h K).homotopyPullbackRightMap p) q)).1).val.2 t =
    ((path q).trans ((K.evalAt q.val.2.1).map h.continuous)) t
  rw [constRightProdHomeomorph_fst_val]
  change pathMap p (.const B' (h b'))
      (((postcompContraction h K).homotopyPullbackRightMap p) q) t = _
  rw [ContinuousMap.Homotopy.pathMap_homotopyPullbackRightMap_apply, postcompContraction_evalAt]
  rfl

/-- **Homotopy pullback along a map out of a contractible corner.** When `[ContractibleSpace B']`,
`HomotopyPullback p h ≃ₕ MappingPathFiber p (h b')` for any chosen point `b' : B'`. -/
noncomputable def mappingPathFiberHomotopyEquiv [ContractibleSpace B']
    (p : C(E, B)) (h : C(B', B)) (b' : B') :
    HomotopyPullback p h ≃ₕ MappingPathFiber p (h b') :=
  mappingPathFiberHomotopyEquivOfContraction p h b' (ContinuousMap.idContraction b')

end ContractibleCorner

end TauCeti.HomotopyPullback

/-! ### Contractible-base and contractible-corner criteria for homotopy-cartesian squares -/

namespace ContinuousMap.Homotopy

open TauCeti

section Squares

variable {E : Type u} {B : Type v} {E' : Type u'} {B' : Type v'}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
  {α : C(E', E)} {p : C(E, B)} {p' : C(E', B')} {h : C(B', B)}

/-- **Squares over a contractible base.** When `[ContractibleSpace B]`, a homotopy-commutative
square `H : (p.comp α).Homotopy (h.comp p')` is homotopy-cartesian if and only if
`α.prodMk p' : C(E', E × B')` is a weak homotopy equivalence. -/
theorem isHomotopyCartesian_iff_prodMk [ContractibleSpace B]
    (H : (p.comp α).Homotopy (h.comp p')) :
    H.IsHomotopyCartesian ↔ (α.prodMk p').IsWeakHomotopyEquivalence := by
  have hπ := HomotopyPullback.isWeakHomotopyEquivalence_prodMk p h
  have hcomp : ((HomotopyPullback.fst p h).prodMk (HomotopyPullback.snd p h)).comp
      (HomotopyPullback.lift α p' H) = α.prodMk p' := by
    ext e' : 1
    simp
  rw [isHomotopyCartesian_iff, ← hcomp]
  exact ⟨fun hL ↦ hπ.comp hL, fun hP ↦ hπ.of_postcomp hP⟩

/-- The comparison map `E' → MappingPathFiber p (h b')` associated to a homotopy-commutative
square `H : (p.comp α).Homotopy (h.comp p')` and a contraction
`K : (.id B').Homotopy (.const B' b')` of the bottom-left corner, sending `e'` to
`(α e', (H.evalAt e').trans ((K.evalAt (p' e')).map h))`. -/
noncomputable def toMappingPathFiberOfContraction (H : (p.comp α).Homotopy (h.comp p'))
    (b' : B') (K : (ContinuousMap.id B').Homotopy (.const B' b')) :
    C(E', MappingPathFiber p (h b')) where
  toFun e' := ⟨(α e',
    ((H.evalAt e').trans ((K.evalAt (p' e')).map h.continuous)).toContinuousMap),
    Path.source _, Path.target _⟩
  continuous_toFun := by
    refine (α.continuous.prodMk ?_).subtype_mk _
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact Path.trans_continuous_family
      (fun e' : E' ↦ H.evalAt e')
      (H.continuous.comp (continuous_snd.prodMk continuous_fst))
      (fun e' : E' ↦ (K.evalAt (p' e')).map h.continuous)
      (h.continuous.comp (K.continuous.comp
        (continuous_snd.prodMk (p'.continuous.comp continuous_fst))))

@[simp]
theorem toMappingPathFiberOfContraction_val_fst (H : (p.comp α).Homotopy (h.comp p'))
    (b' : B') (K : (ContinuousMap.id B').Homotopy (.const B' b')) (e' : E') :
    (H.toMappingPathFiberOfContraction b' K e').val.1 = α e' :=
  (rfl)

@[simp]
theorem toMappingPathFiberOfContraction_val_snd_apply (H : (p.comp α).Homotopy (h.comp p'))
    (b' : B') (K : (ContinuousMap.id B').Homotopy (.const B' b')) (e' : E') (t : I) :
    (H.toMappingPathFiberOfContraction b' K e').val.2 t =
      ((H.evalAt e').trans ((K.evalAt (p' e')).map h.continuous)) t :=
  (rfl)

@[simp]
theorem proj_comp_toMappingPathFiberOfContraction (H : (p.comp α).Homotopy (h.comp p'))
    (b' : B') (K : (ContinuousMap.id B').Homotopy (.const B' b')) :
    (MappingPathFiber.proj p (h b')).comp (H.toMappingPathFiberOfContraction b' K) = α := by
  ext : 1; simp

@[simp]
theorem mappingPathFiberHomotopyEquivOfContraction_comp_lift
    (H : (p.comp α).Homotopy (h.comp p')) (b' : B')
    (K : (ContinuousMap.id B').Homotopy (.const B' b')) :
    (HomotopyPullback.mappingPathFiberHomotopyEquivOfContraction p h b' K).toFun.comp
      (HomotopyPullback.lift α p' H) = H.toMappingPathFiberOfContraction b' K := by
  ext e' : 1
  apply Subtype.ext
  refine Prod.ext (by simp) ?_
  ext t : 1
  let r := HomotopyPullback.lift α p' H e'
  change (HomotopyPullback.mappingPathFiberHomotopyEquivOfContraction p h b' K r).val.2 t =
    ((H.evalAt e').trans ((K.evalAt (p' e')).map h.continuous)) t
  rw [HomotopyPullback.mappingPathFiberHomotopyEquivOfContraction_val_snd_apply]
  have hpath (u : I) : HomotopyPullback.path r u = H (u, e') := by
    rw [HomotopyPullback.path_apply, HomotopyPullback.pathMap_lift_apply]
  have hsnd : r.val.2.1 = p' e' := by
    rw [HomotopyPullback.lift_val]
  exact path_trans_apply_congr _ _ _ _ (fun u ↦ hpath u)
    (fun u ↦ by change h (K (u, r.val.2.1)) = h (K (u, p' e')); rw [hsnd]) t

/-- **Contractible-corner criterion for homotopy-cartesian squares (explicit contraction).** Given
`H : (p.comp α).Homotopy (h.comp p')` and a contraction `K : (.id B').Homotopy (.const B' b')`, the
square `H` is homotopy-cartesian if and only if
`H.toMappingPathFiberOfContraction b' K : C(E', MappingPathFiber p (h b'))` is a weak homotopy
equivalence. -/
theorem isHomotopyCartesian_iff_of_contraction (H : (p.comp α).Homotopy (h.comp p'))
    (b' : B') (K : (ContinuousMap.id B').Homotopy (.const B' b')) :
    H.IsHomotopyCartesian ↔
      (H.toMappingPathFiberOfContraction b' K).IsWeakHomotopyEquivalence := by
  have he :=
    (HomotopyPullback.mappingPathFiberHomotopyEquivOfContraction p h b'
      K).isWeakHomotopyEquivalence
  rw [isHomotopyCartesian_iff, ← H.mappingPathFiberHomotopyEquivOfContraction_comp_lift b' K]
  exact ⟨fun hL ↦ he.comp hL, fun hF ↦ he.of_postcomp hF⟩

/-- The comparison map `E' → MappingPathFiber p (h b')` associated to `H` when
`[ContractibleSpace B']`, using `ContinuousMap.idContraction b'`. -/
noncomputable def toMappingPathFiber [ContractibleSpace B']
    (H : (p.comp α).Homotopy (h.comp p')) (b' : B') :
    C(E', MappingPathFiber p (h b')) :=
  H.toMappingPathFiberOfContraction b' (ContinuousMap.idContraction b')

@[simp]
theorem proj_comp_toMappingPathFiber [ContractibleSpace B']
    (H : (p.comp α).Homotopy (h.comp p')) (b' : B') :
    (MappingPathFiber.proj p (h b')).comp (H.toMappingPathFiber b') = α :=
  H.proj_comp_toMappingPathFiberOfContraction b' _

/-- **Contractible-corner criterion for homotopy-cartesian squares.** When `[ContractibleSpace B']`,
`H : (p.comp α).Homotopy (h.comp p')` is homotopy-cartesian if and only if, for a chosen point
`b' : B'`, the induced map `H.toMappingPathFiber b' : C(E', MappingPathFiber p (h b'))` is a weak
homotopy equivalence. -/
theorem isHomotopyCartesian_iff_toMappingPathFiber [ContractibleSpace B']
    (H : (p.comp α).Homotopy (h.comp p')) (b' : B') :
    H.IsHomotopyCartesian ↔ (H.toMappingPathFiber b').IsWeakHomotopyEquivalence :=
  H.isHomotopyCartesian_iff_of_contraction b' (ContinuousMap.idContraction b')

/-- **Criterion with both left-hand corners contractible.** When both `E'` and `B'` are
contractible, `H : (p.comp α).Homotopy (h.comp p')` is homotopy-cartesian if and only if
`MappingPathFiber p (h b')` is weakly contractible (its collapse map to `Unit` is a weak homotopy
equivalence). -/
theorem isHomotopyCartesian_iff_const_mappingPathFiber
    [ContractibleSpace E'] [ContractibleSpace B']
    (H : (p.comp α).Homotopy (h.comp p')) (b' : B') :
    H.IsHomotopyCartesian ↔
      (ContinuousMap.const (MappingPathFiber p (h b')) ()).IsWeakHomotopyEquivalence := by
  have hE' : (ContinuousMap.const E' ()).IsWeakHomotopyEquivalence :=
    ContinuousMap.isWeakHomotopyEquivalence_of_contractibleSpace _
  have hcomp :
      (ContinuousMap.const (MappingPathFiber p (h b')) ()).comp (H.toMappingPathFiber b') =
        ContinuousMap.const E' () := by
    ext : 1; rfl
  rw [H.isHomotopyCartesian_iff_toMappingPathFiber b']
  exact ⟨fun hf ↦ hf.of_precomp (hcomp.symm ▸ hE'),
    fun hc ↦ hc.of_postcomp (hcomp.symm ▸ hE')⟩

end Squares

end ContinuousMap.Homotopy

/-! ### Strict-square and `TopCat` specializations, and the point-inclusion check -/

namespace TauCeti

section StrictContractible

variable {E : Type u} {B : Type v} {E' : Type u'} {B' : Type v'}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
  {α : C(E', E)} {p : C(E, B)} {p' : C(E', B')} {h : C(B', B)}

/-- Over a contractible base `B`, a strictly commuting square `p.comp α = h.comp p'` is
homotopy-cartesian if and only if `α.prodMk p'` is a weak homotopy equivalence. -/
theorem isHomotopyCartesian_iff_prodMk [ContractibleSpace B] (hcomm : p.comp α = h.comp p') :
    IsHomotopyCartesian hcomm ↔ (α.prodMk p').IsWeakHomotopyEquivalence := by
  rw [isHomotopyCartesian_iff_homotopy]
  exact ContinuousMap.Homotopy.isHomotopyCartesian_iff_prodMk _

/-- For a strictly commuting square `hcomm : p.comp α = h.comp p'` and a contraction
`K : (.id B').Homotopy (.const B' b')`, the comparison map `E' → MappingPathFiber p (h b')`
sending `e'` directly to `(α e', (K.evalAt (p' e')).map h)` without an initial constant-path
segment. -/
def toMappingPathFiberOfContraction (hcomm : p.comp α = h.comp p')
    (b' : B') (K : (ContinuousMap.id B').Homotopy (.const B' b')) :
    C(E', MappingPathFiber p (h b')) where
  toFun e' := ⟨(α e',
    (((K.evalAt (p' e')).map h.continuous).cast
      (ContinuousMap.congr_fun hcomm e') rfl).toContinuousMap),
    Path.source _, Path.target _⟩
  continuous_toFun := by
    refine (α.continuous.prodMk ?_).subtype_mk _
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact h.continuous.comp (K.continuous.comp
      (continuous_snd.prodMk (p'.continuous.comp continuous_fst)))

@[simp]
theorem toMappingPathFiberOfContraction_val_fst (hcomm : p.comp α = h.comp p')
    (b' : B') (K : (ContinuousMap.id B').Homotopy (.const B' b')) (e' : E') :
    (toMappingPathFiberOfContraction hcomm b' K e').val.1 = α e' :=
  (rfl)

@[simp]
theorem toMappingPathFiberOfContraction_val_snd_apply (hcomm : p.comp α = h.comp p')
    (b' : B') (K : (ContinuousMap.id B').Homotopy (.const B' b')) (e' : E') (t : I) :
    (toMappingPathFiberOfContraction hcomm b' K e').val.2 t = h (K (t, p' e')) :=
  (rfl)

@[simp]
theorem proj_comp_toMappingPathFiberOfContraction (hcomm : p.comp α = h.comp p')
    (b' : B') (K : (ContinuousMap.id B').Homotopy (.const B' b')) :
    (MappingPathFiber.proj p (h b')).comp (toMappingPathFiberOfContraction hcomm b' K) = α := by
  ext : 1; simp

/-- Prepending the constant homotopy in `Homotopy.toMappingPathFiberOfContraction` is homotopic to
`TauCeti.toMappingPathFiberOfContraction` via `Path.delayReflLeft`. -/
theorem homotopy_toMappingPathFiberOfContraction_refl (hcomm : p.comp α = h.comp p')
    (b' : B') (K : (ContinuousMap.id B').Homotopy (.const B' b')) :
    (((ContinuousMap.Homotopy.refl (p.comp α)).cast rfl hcomm).toMappingPathFiberOfContraction
      b' K).Homotopic (toMappingPathFiberOfContraction hcomm b' K) := by
  let γ (e' : E') : Path (p (α e')) (h b') :=
    ((K.evalAt (p' e')).map h.continuous).cast (ContinuousMap.congr_fun hcomm e') rfl
  have hγ : Continuous ↿γ :=
    h.continuous.comp (K.continuous.comp
      (continuous_snd.prodMk (p'.continuous.comp continuous_fst)))
  refine ⟨{
    toFun q := ⟨(α q.2, (Path.delayReflLeft q.1 (γ q.2)).toContinuousMap),
      Path.source _, Path.target _⟩
    continuous_toFun := by
      refine ((α.continuous.comp continuous_snd).prodMk ?_).subtype_mk _
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact Path.delayReflLeft_continuous_family (fun q : I × E' ↦ γ q.2)
        (hγ.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
        ContinuousMap.fst
    map_zero_left e' := by
      apply Subtype.ext
      refine Prod.ext rfl ?_
      ext t : 1
      have h0 := congrArg (fun δ : Path (p (α e')) (h b') ↦ δ t)
        (Path.delayReflLeft_zero (γ e'))
      refine h0.trans ?_
      change ((Path.refl (p (α e'))).trans (γ e')) t =
        ((((ContinuousMap.Homotopy.refl (p.comp α)).cast rfl hcomm).toMappingPathFiberOfContraction
          b' K e').val.2) t
      rw [ContinuousMap.Homotopy.toMappingPathFiberOfContraction_val_snd_apply]
      exact path_trans_apply_congr _ _ _ _ (fun _ ↦ rfl) (fun _ ↦ rfl) t
    map_one_left e' := by
      apply Subtype.ext
      refine Prod.ext rfl ?_
      ext t : 1
      exact congrArg (fun δ : Path (p (α e')) (h b') ↦ δ t)
        (Path.delayReflLeft_one (γ e')) }⟩

/-- **Contractible-corner criterion for strictly commuting squares (explicit contraction).** -/
theorem isHomotopyCartesian_iff_of_contraction (hcomm : p.comp α = h.comp p')
    (b' : B') (K : (ContinuousMap.id B').Homotopy (.const B' b')) :
    IsHomotopyCartesian hcomm ↔
      (toMappingPathFiberOfContraction hcomm b' K).IsWeakHomotopyEquivalence := by
  rw [isHomotopyCartesian_iff_homotopy,
    ContinuousMap.Homotopy.isHomotopyCartesian_iff_of_contraction _ b' K]
  exact ⟨fun hf ↦ hf.of_homotopic (homotopy_toMappingPathFiberOfContraction_refl hcomm b' K),
    fun hf ↦ hf.of_homotopic (homotopy_toMappingPathFiberOfContraction_refl hcomm b' K).symm⟩

/-- Comparison map `E' → MappingPathFiber p (h b')` for a strictly commuting square when
`[ContractibleSpace B']`. -/
noncomputable def toMappingPathFiber [ContractibleSpace B']
    (hcomm : p.comp α = h.comp p') (b' : B') :
    C(E', MappingPathFiber p (h b')) :=
  toMappingPathFiberOfContraction hcomm b' (ContinuousMap.idContraction b')

/-- **Contractible-corner criterion for strictly commuting squares.** -/
theorem isHomotopyCartesian_iff_toMappingPathFiber [ContractibleSpace B']
    (hcomm : p.comp α = h.comp p') (b' : B') :
    IsHomotopyCartesian hcomm ↔
      (toMappingPathFiber hcomm b').IsWeakHomotopyEquivalence :=
  isHomotopyCartesian_iff_of_contraction hcomm b' (ContinuousMap.idContraction b')

/-- The canonical strict square exhibiting the strict fibre `p ⁻¹' {b}` over `Unit → B` at
`b`. -/
theorem fiberSquare_comm (p : C(E, B)) (b : B) :
    p.comp ⟨Subtype.val, continuous_subtype_val⟩ =
      (ContinuousMap.const Unit b).comp (.const ↥(p ⁻¹' {b}) ()) :=
  ContinuousMap.ext fun x ↦ x.2

/-- Specializing `toMappingPathFiberOfContraction` to `B' = Unit` and `h = .const Unit b` recovers
the constant-path fibre inclusion `MappingPathFiber.ofFiber p b` on the nose. -/
@[simp]
theorem toMappingPathFiberOfContraction_fiberSquare (p : C(E, B)) (b : B) :
    toMappingPathFiberOfContraction (fiberSquare_comm p b) ()
      ((ContinuousMap.Homotopy.refl (.id Unit)).cast rfl (ContinuousMap.ext fun _ ↦ rfl)) =
      MappingPathFiber.ofFiber p b := by
  ext x : 1
  apply Subtype.ext
  change (toMappingPathFiberOfContraction (fiberSquare_comm p b) ()
      ((ContinuousMap.Homotopy.refl (.id Unit)).cast rfl (ContinuousMap.ext fun _ ↦ rfl)) x).val =
    (MappingPathFiber.ofFiber p b x).val
  rw [MappingPathFiber.ofFiber_val]
  refine Prod.ext rfl ?_
  ext _ : 1
  rfl

/-- **Point-inclusion specialization.** The strict fibre square of `p ⁻¹' {b}` over `Unit → B`
at `b` is homotopy-cartesian if and only if `MappingPathFiber.ofFiber p b` is a weak homotopy
equivalence. -/
theorem isHomotopyCartesian_fiber_iff_ofFiber (p : C(E, B)) (b : B) :
    IsHomotopyCartesian (fiberSquare_comm p b) ↔
      (MappingPathFiber.ofFiber p b).IsWeakHomotopyEquivalence := by
  rw [isHomotopyCartesian_iff_of_contraction (fiberSquare_comm p b) ()
      ((ContinuousMap.Homotopy.refl (.id Unit)).cast rfl (ContinuousMap.ext fun _ ↦ rfl)),
    toMappingPathFiberOfContraction_fiberSquare]
  exact Iff.rfl

end StrictContractible

end TauCeti

namespace CategoryTheory.CommSq

open TauCeti

variable {E B E' B' : TopCat.{u}} {α : E' ⟶ E} {p' : E' ⟶ B'} {p : E ⟶ B} {h : B' ⟶ B}

/-- Over a contractible base `B`, `sq : CommSq α p' p h` in `TopCat` is homotopy-cartesian if and
only if `α.hom.prodMk p'.hom` is a weak homotopy equivalence. -/
theorem isHomotopyCartesian_iff_prodMk [ContractibleSpace B] (sq : CommSq α p' p h) :
    sq.IsHomotopyCartesian ↔ (α.hom.prodMk p'.hom).IsWeakHomotopyEquivalence := by
  rw [isHomotopyCartesian_iff]
  exact TauCeti.isHomotopyCartesian_iff_prodMk (congrArg TopCat.Hom.hom sq.w)

/-- **Contractible-corner criterion for `CommSq` in `TopCat` (explicit contraction).** -/
theorem isHomotopyCartesian_iff_of_contraction (sq : CommSq α p' p h)
    (b' : B') (K : (ContinuousMap.id B').Homotopy (.const B' b')) :
    sq.IsHomotopyCartesian ↔
      (TauCeti.toMappingPathFiberOfContraction
        (congrArg TopCat.Hom.hom sq.w) b' K).IsWeakHomotopyEquivalence := by
  rw [isHomotopyCartesian_iff]
  exact TauCeti.isHomotopyCartesian_iff_of_contraction (congrArg TopCat.Hom.hom sq.w) b' K

/-- **Contractible-corner criterion for `CommSq` in `TopCat`.** -/
theorem isHomotopyCartesian_iff_toMappingPathFiber [ContractibleSpace B']
    (sq : CommSq α p' p h) (b' : B') :
    sq.IsHomotopyCartesian ↔
      (TauCeti.toMappingPathFiber (congrArg TopCat.Hom.hom sq.w) b').IsWeakHomotopyEquivalence := by
  rw [isHomotopyCartesian_iff]
  exact TauCeti.isHomotopyCartesian_iff_toMappingPathFiber (congrArg TopCat.Hom.hom sq.w) b'

end CategoryTheory.CommSq
