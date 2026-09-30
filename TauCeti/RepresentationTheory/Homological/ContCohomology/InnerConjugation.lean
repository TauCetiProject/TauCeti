/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete

/-!
# Inner automorphisms act trivially on continuous cohomology

Let `G` be a locally compact topological group, `X` a smooth discrete topological representation
of `G`, and let `g : G`. The compatible pair consisting of the inner automorphism
`x ↦ g⁻¹ * x * g` of `G` and the
action `X.ρ g` of `g` on the coefficients induces an endomorphism of `Hⁿ(G, X)`, the conjugation
map `g_*` of Neukirch–Schmidt–Wingberg (Chapter I, §5). This file proves that it is the identity
in every degree (`TauCeti.ContinuousCohomology.map_eq_id_of_inner`), for Mathlib's canonical
`continuousCohomology`.

## The argument

Mathlib computes `Hⁿ(G, X)` from the coinduced resolution `Xₙ = C(G, C(G, …, C(G, X)))`, whose
differential is the recursion `(d F) x = F - d (F x)`; the homogeneous `n`-cochains are the
`G`-invariant elements of `Xₙ₊₁`. On such an invariant element the cochain map of the compatible
pair is **right translation of every argument** by `g`,

```text
F (x₀, …, xₙ) ↦ F (x₀ * g, …, xₙ * g),
```

because invariance turns `g • F (g⁻¹ * x₀ * g, …)` into `F (x₀ * g, …)`
(`TauCeti.ContinuousCohomology.resolutionMap_hom_apply_eq_resolutionTranslate`). Right translation
by `a` makes sense on the whole resolution, as the `G`-equivariant chain map
`TauCeti.ContinuousCohomology.resolutionTranslate`, `(T F) x = T (F (x * a))`, and it is
chain-homotopic to the identity through the **prism operator**
`TauCeti.ContinuousCohomology.translateHomotopy`,

```text
(h F) (x₀, …, xₙ₋₁) = ∑ᵢ (-1)ⁱ F (x₀, …, xᵢ, xᵢ * a, …, xₙ₋₁ * a),
```

which on the curried resolution is the recursion `(h F) x = T (F x (x * a)) - h (F x)`. The
homotopy identity `d (h F) + h (d F) = T F - F`
(`TauCeti.ContinuousCohomology.d_translateHomotopy_add_translateHomotopy_d`) holds for every
element of the resolution, invariant or not, and `h` is `G`-equivariant, so for a homogeneous
cocycle `z` the difference `T z - z` is the coboundary of the homogeneous cochain `h z`.

The prism operator evaluates a curried cochain along the graph `x ↦ (x, x * a)`, and it is
continuous in `F` because uncurrying `C(G, C(G, Y)) → C(G × G, Y)` is continuous; that is where
local compactness of `G` is used, and it is the only hypothesis beyond Mathlib's standing ones.
Every profinite group is compact, hence locally compact.

## Main definitions

* `TauCeti.ContinuousCohomology.resolutionTranslate`: right translation of every argument by
  `a`, as an endomorphism of each term of the coinduced resolution.
* `TauCeti.ContinuousCohomology.translateHomotopy`: the prism operator, a chain homotopy from the
  identity to `resolutionTranslate`.

## Main results

* `TauCeti.ContinuousCohomology.resolutionTranslate_d_apply`: right translation is a chain map.
* `TauCeti.ContinuousCohomology.d_translateHomotopy_add_translateHomotopy_d`: the homotopy
  identity `d (h F) + h (d F) = T F - F`.
* `TauCeti.ContinuousCohomology.translateHomotopy_ρ`: the prism operator is `G`-equivariant.
* `TauCeti.ContinuousCohomology.map_eq_id_of_inner`: **inner automorphisms act trivially on
  continuous cohomology in every degree.**

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter I, §5,
  for the conjugation maps `g_*`.
* K. S. Brown, *Cohomology of Groups*, GTM 87, Chapter III, §8, for the triviality of inner
  conjugation on the cohomology of a discrete group.
-/

public section

open CategoryTheory

namespace TauCeti.ContinuousCohomology

open _root_.ContinuousCohomology TopRep

variable {k : Type*} [Ring k] [TopologicalSpace k] {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (X : TopRep k G) (a : G)

/-! ### Right translation on the coinduced resolution -/

/-- **Right translation on the coinduced resolution**: the endomorphism of the `n`-th term
`C(G, C(G, …, C(G, X)))` translating every argument on the right by `a`,
`F (x₁, …, xₙ) ↦ F (x₁ * a, …, xₙ * a)`, defined by the recursion `(T F) x = T (F (x * a))`.
Left and right translations commute, so it is `G`-equivariant. -/
noncomputable def resolutionTranslate : (n : ℕ) → resolutionX X n ⟶ resolutionX X n
  | 0 => 𝟙 X
  | n + 1 => ofHom
      { toFun F := ((resolutionTranslate n).hom : C((resolutionX X n).V, (resolutionX X n).V)).comp
          ((F : C(G, (resolutionX X n).V)).comp (ContinuousMap.mulRight a))
        map_add' _ _ := by ext; simp
        map_smul' _ _ := by ext; simp
        isIntertwining' g := by
          ext F x
          simp [hom_comm_apply, mul_assoc]
        cont := (ContinuousMap.continuous_postcomp _).comp (ContinuousMap.continuous_precomp _) }

@[simp]
theorem resolutionTranslate_zero : resolutionTranslate X a 0 = 𝟙 X :=
  (rfl)

/-- Right translation on a successor term of the resolution, at a point:
`(T F) x = T (F (x * a))`. -/
@[simp]
theorem resolutionTranslate_succ_apply (n : ℕ) (F : (resolutionX X (n + 1)).V) (x : G) :
    ((resolutionTranslate X a (n + 1)).hom F) x = (resolutionTranslate X a n).hom (F (x * a)) :=
  (rfl)

/-- Translation by the identity acts as the identity on every term of the resolution. -/
@[simp]
theorem resolutionTranslate_one (n : ℕ) : resolutionTranslate X 1 n = 𝟙 _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext F x
    simp only [ContIntertwiningMap.toContinuousLinearMap_apply]
    rw [TopRep.id_apply, resolutionTranslate_succ_apply, mul_one, ih, TopRep.id_apply]

/-- Translation by a product is the composite of the two right translations. -/
theorem resolutionTranslate_mul (b : G) (n : ℕ) :
    resolutionTranslate X (a * b) n = resolutionTranslate X b n ≫ resolutionTranslate X a n := by
  induction n with
  | zero => simp
  | succ n ih =>
    ext F x
    simp only [ContIntertwiningMap.toContinuousLinearMap_apply]
    rw [ConcreteCategory.comp_apply, resolutionTranslate_succ_apply,
      resolutionTranslate_succ_apply, resolutionTranslate_succ_apply, mul_assoc, ih,
      ConcreteCategory.comp_apply]

/-- **Right translation is a chain map**: it commutes with the differential of the coinduced
resolution. -/
theorem resolutionTranslate_d_apply (n : ℕ) (v : (resolutionX X n).V) :
    (resolutionTranslate X a (n + 1)).hom ((d X n).hom v) =
      (d X n).hom ((resolutionTranslate X a n).hom v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine ContinuousMap.ext fun x => ?_
    rw [resolutionTranslate_succ_apply, hom_d_succ_apply_apply, hom_d_succ_apply_apply, map_sub,
      resolutionTranslate_succ_apply, ih]

/-! ### The prism operator -/

section Homotopy

variable [LocallyCompactSpace G]

/-- **The prism operator** of right translation by `a`, from the `(n + 1)`-st to the `n`-th term
of the coinduced resolution. In uncurried form it is
`(h F) (x₀, …, xₙ₋₁) = ∑ᵢ (-1)ⁱ F (x₀, …, xᵢ, xᵢ * a, …, xₙ₋₁ * a)`; on the curried resolution it
is the recursion `(h F) x = T (F x (x * a)) - h (F x)` with `T = resolutionTranslate X a`, starting
from `h = 0`. It is a chain homotopy from the identity to `T`
(`d_translateHomotopy_add_translateHomotopy_d`). Evaluating along the graph `x ↦ (x, x * a)` is
continuous in `F` because `G` is locally compact. -/
noncomputable def translateHomotopy :
    (n : ℕ) → (resolutionX X (n + 1)).V →L[k] (resolutionX X n).V
  | 0 => 0
  | n + 1 =>
    { toFun F :=
        ((resolutionTranslate X a n).hom : C((resolutionX X n).V, (resolutionX X n).V)).comp
            ((ContinuousMap.uncurry (F : C(G, C(G, (resolutionX X n).V)))).comp
              ((ContinuousMap.id G).prodMk (ContinuousMap.mulRight a))) -
          (translateHomotopy n : C((resolutionX X (n + 1)).V, (resolutionX X n).V)).comp F
      map_add' _ _ := by
        ext
        simp only [ContinuousMap.sub_apply, ContinuousMap.comp_apply, ContinuousMap.uncurry_apply,
          ContinuousMap.prod_eval, Function.uncurry_apply_pair, ContinuousMap.coe_coe,
          ContinuousMap.add_apply, map_add]
        abel
      map_smul' _ _ := by
        ext
        simp only [ContinuousMap.sub_apply, ContinuousMap.comp_apply, ContinuousMap.uncurry_apply,
          ContinuousMap.prod_eval, Function.uncurry_apply_pair, ContinuousMap.coe_coe,
          ContinuousMap.smul_apply, map_smul, RingHom.id_apply, smul_sub]
      cont :=
        ((ContinuousMap.continuous_postcomp _).comp
            ((ContinuousMap.continuous_precomp _).comp ContinuousMap.continuous_uncurry)).sub
          (ContinuousMap.continuous_postcomp _) }

@[simp]
theorem translateHomotopy_zero : translateHomotopy X a 0 = 0 :=
  (rfl)

/-- The prism operator on a successor term, at a point: `(h F) x = T (F x (x * a)) - h (F x)`. -/
@[simp]
theorem translateHomotopy_succ_apply (n : ℕ) (F : (resolutionX X (n + 1 + 1)).V) (x : G) :
    (translateHomotopy X a (n + 1) F) x =
      (resolutionTranslate X a n).hom (F x (x * a)) - translateHomotopy X a n (F x) :=
  (rfl)

private theorem translateHomotopy_identity_succ_apply (n : ℕ)
    (F : (resolutionX X (n + 1 + 1)).V) (x : G)
    (ih : ∀ (v : (resolutionX X (n + 1)).V),
      (d X n).hom (translateHomotopy X a n v) +
          translateHomotopy X a (n + 1) ((d X (n + 1)).hom v) =
        (resolutionTranslate X a (n + 1)).hom v - v) :
    ((d X (n + 1)).hom (translateHomotopy X a (n + 1) F) +
      translateHomotopy X a (n + 1 + 1) ((d X (n + 1 + 1)).hom F)) x =
      ((resolutionTranslate X a (n + 1 + 1)).hom F - F) x := by
  have hcancel := eq_sub_of_add_eq' (ih (F x))
  rw [ContinuousMap.add_apply, hom_d_succ_apply_apply, translateHomotopy_succ_apply,
    translateHomotopy_succ_apply, hom_d_succ_apply_apply, map_sub, ContinuousMap.sub_apply,
    hom_d_succ_apply_apply]
  simp only [map_sub]
  rw [resolutionTranslate_d_apply, ContinuousMap.sub_apply, resolutionTranslate_succ_apply,
    hcancel]
  abel

/-- **The homotopy identity** `d (h F) + h (d F) = T F - F`: the prism operator is a chain homotopy
from the identity to right translation. It holds for every element of the resolution, invariant or
not. -/
theorem d_translateHomotopy_add_translateHomotopy_d (n : ℕ) (F : (resolutionX X (n + 1)).V) :
    (d X n).hom (translateHomotopy X a n F) +
        translateHomotopy X a (n + 1) ((d X (n + 1)).hom F) =
      (resolutionTranslate X a (n + 1)).hom F - F := by
  induction n with
  | zero =>
    refine ContinuousMap.ext fun x => ?_
    rw [ContinuousMap.add_apply, translateHomotopy_succ_apply, hom_d_succ_apply_apply,
      ContinuousMap.sub_apply, ContinuousMap.sub_apply, resolutionTranslate_succ_apply,
      translateHomotopy_zero]
    simp [d_zero, ContIntertwiningMap.id_apply]
  | succ n ih =>
    exact ContinuousMap.ext fun x => translateHomotopy_identity_succ_apply X a n F x ih

/-- **The prism operator is `G`-equivariant**, because left and right translations commute. -/
theorem translateHomotopy_ρ (n : ℕ) (g : G) (F : (resolutionX X (n + 1)).V) :
    translateHomotopy X a n ((resolutionX X (n + 1)).ρ g F) =
      (resolutionX X n).ρ g (translateHomotopy X a n F) := by
  induction n with
  | zero => simp
  | succ n ih =>
    refine ContinuousMap.ext fun x => ?_
    rw [translateHomotopy_succ_apply, resolutionX_succ_ρ_apply_apply,
      resolutionX_succ_ρ_apply_apply, resolutionX_succ_ρ_apply_apply,
      translateHomotopy_succ_apply, map_sub, ih, mul_assoc, hom_comm_apply]

/-- The prism operator preserves `G`-invariant elements, that is, homogeneous cochains. -/
theorem translateHomotopy_mem_invariants {n : ℕ} {F : (resolutionX X (n + 1)).V}
    (hF : F ∈ (resolutionX X (n + 1)).ρ.invariants) :
    translateHomotopy X a n F ∈ (resolutionX X n).ρ.invariants :=
  (ContRepresentation.mem_invariants _).2 fun g => by
    rw [← translateHomotopy_ρ, (ContRepresentation.mem_invariants F).1 hF g]

/-- On an element killed by the differential, right translation differs from the identity by the
differential of the prism operator. -/
theorem resolutionTranslate_sub_self_of_d_eq_zero {n : ℕ} {F : (resolutionX X (n + 1)).V}
    (hF : (d X (n + 1)).hom F = 0) :
    (resolutionTranslate X a (n + 1)).hom F - F = (d X n).hom (translateHomotopy X a n F) := by
  rw [← d_translateHomotopy_add_translateHomotopy_d, hF, map_zero, add_zero]

end Homotopy

/-! ### Inner conjugation on cohomology -/

section Inner

variable {X} (g : G) (φ : G →ₜ* G) (hφ : ∀ x, φ x = g⁻¹ * x * g)
  (f : TopRep.res (φ : G →* G) X ⟶ X) (hf : ∀ v, f.hom v = X.ρ g v)

include hφ hf

/-- On the coinduced resolution, the map of the inner compatible pair `(x ↦ g⁻¹ * x * g, X.ρ g)`
is right translation by `g` after the action of `g`. In particular it is right translation by `g`
on `G`-invariant elements. -/
theorem resolutionMap_hom_apply_eq_resolutionTranslate (n : ℕ) (F : (resolutionX X n).V) :
    (resolutionMap φ f n).hom F =
      (resolutionTranslate X g n).hom ((resolutionX X n).ρ g F) := by
  induction n with
  | zero => exact hf F
  | succ n ih =>
    refine ContinuousMap.ext fun x => ?_
    rw [resolutionTranslate_succ_apply, resolutionX_succ_ρ_apply_apply, ← mul_assoc, ← hφ]
    exact ih (F (φ x))

variable [LocallyCompactSpace G]

/-- **Inner automorphisms act trivially on continuous cohomology.** For `g : G`, the compatible
pair consisting of the inner automorphism `x ↦ g⁻¹ * x * g` of `G` and the action of `g` on the
coefficients, which is NSW's conjugation `g_*`, induces the identity of `Hⁿ(G, X)` in every degree.
The homomorphism and the coefficient map are taken as hypotheses on their values, so that the
statement applies to any presentation of the pair. The coefficient representation is smooth
discrete: its underlying module has the discrete topology and every point stabilizer is open. -/
theorem map_eq_id_of_inner (_hX : IsSmoothDiscrete k X) (n : ℕ) :
    map φ f n = 𝟙 (continuousCohomology n X) := by
  classical
  let K := homogeneousCochains X
  -- Restrict the prism operator to homogeneous cochains.
  let h : ∀ i j, (ComplexShape.up ℕ).Rel j i → (K.X i ⟶ K.X j) := fun i j hij => by
    obtain rfl := hij
    exact TopModuleCat.ofHom ((translateHomotopy X g (j + 1)).restrict
      (fun _ hv => translateHomotopy_mem_invariants X g hv))
  -- The prism identity identifies the difference with Mathlib's null-homotopic map.
  have heq : cochainsMap φ f - 𝟙 K = Homotopy.nullHomotopicMap' h := by
    ext i v : 3
    apply Subtype.ext
    simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f]
    have hs := TopModuleCat.hom_sub k ((cochainsMap φ f).f i) (𝟙 (K.X i))
    dsimp only [TopModuleCat.Hom.hom] at hs
    rw [hs, sub_apply,
      TopModuleCat.hom_id k (K.X i), ContinuousLinearMap.id_apply, Submodule.coe_sub,
      coe_cochainsMap_f_apply,
      resolutionMap_hom_apply_eq_resolutionTranslate g φ hφ f hf,
      (ContRepresentation.mem_invariants _).1 v.2 g]
    have hh (j : ℕ) (w : K.X (j + 1)) :
        (h (j + 1) j (ComplexShape.up_mk _ _ rfl) w).1 = translateHomotopy X g (j + 1) w.1 := rfl
    have hd (j : ℕ) (w : K.X j) :
        (K.d j (j + 1) w).1 = (d X (j + 1)).hom w.1 :=
      homogeneousCochains.d_apply X j w
    cases i with
    | zero =>
      rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right
        (ComplexShape.up_mk 0 1 rfl) (by simp)]
      simp only [ConcreteCategory.comp_apply]
      rw [hh, hd]
      have hid := d_translateHomotopy_add_translateHomotopy_d X g 0 v.1
      simpa only [translateHomotopy_zero, zero_apply, map_zero, zero_add]
        using hid.symm
    | succ i =>
      rw [Homotopy.nullHomotopicMap'_f
        (ComplexShape.up_mk i (i + 1) rfl)
        (ComplexShape.up_mk (i + 1) (i + 1 + 1) rfl)]
      have ha := TopModuleCat.hom_add k
        (K.d (i + 1) (i + 1 + 1) ≫ h _ _ (ComplexShape.up_mk _ _ rfl))
        (h _ _ (ComplexShape.up_mk _ _ rfl) ≫ K.d i (i + 1))
      dsimp only [TopModuleCat.Hom.hom] at ha
      rw [ha, add_apply, Submodule.coe_add]
      simp only [ConcreteCategory.comp_apply]
      rw [hh, hd, hd, hh]
      exact (d_translateHomotopy_add_translateHomotopy_d X g (i + 1) v.1).symm.trans
        (add_comm _ _)
  have ho : Homotopy (cochainsMap φ f) (𝟙 K) :=
    Homotopy.equivSubZero.symm
      (heq.symm ▸ Homotopy.nullHomotopy' h)
  exact (ho.homologyMap_eq n).trans (HomologicalComplex.homologyMap_id K n)

end Inner

end TauCeti.ContinuousCohomology
