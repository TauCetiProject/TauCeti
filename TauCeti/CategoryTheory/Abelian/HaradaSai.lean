/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import TauCeti.CategoryTheory.Abelian.Length
public import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Basic
public import TauCeti.CategoryTheory.Preadditive.Radical.Basic
import TauCeti.CategoryTheory.Preadditive.Indecomposable
import TauCeti.CategoryTheory.Preadditive.Radical.Chain

/-!
# The Harada–Sai lemma

Let `C` be an abelian category, and let `X₀ ⟶ X₁ ⟶ ⋯ ⟶ Xₙ` be a chain of non-isomorphisms between
indecomposable objects of finite length, each of length at most `b`, where the length
`CategoryTheory.length` of an object is the length of its composition series. The **Harada–Sai
lemma** says that the composite vanishes as soon as `n ≥ 2 ^ b - 1`. It is the basic finiteness
statement of Auslander–Reiten theory. In a Krull-Schmidt length category, an abelian category whose
objects all have finite length, whose indecomposable objects have length at most `b`, for instance
the finitely generated modules over a representation-finite algebra, it makes the
`(2 ^ b - 1)`-th power of the radical vanish
(`TauCeti.jacobsonRadicalIdeal_pow_eq_bot_of_length_le`); and it is the first step towards
Auslander's theorem and the first Brauer–Thrall conjecture. For modules, the length of an object of
`ModuleCat A` is the length of the module (`ModuleCat.length_eq`).

A chain of morphisms is encoded as a functor `F : ℕ ⥤ C`: the morphism `i ⟶ j` of `ℕ` is sent to
the composite `F.obj i ⟶ F.obj j`, and `F.map (homOfLE (Nat.le_add_right i 1))` is the `i`-th link.
A sequence of morphisms `f i : X i ⟶ X (i + 1)` gives such a functor through Mathlib's
`CategoryTheory.Functor.ofSequence`, whose value on `0 ⟶ n` is the composite of the first `n`
links. A finite chain of `n` links is Mathlib's `CategoryTheory.ComposableArrows`, a functor
`Fin (n + 1) ⥤ C` whose composite is `F.hom`.

## Main results

* `TauCeti.isIso_of_length_image_le_length_image_comp`: the inductive step. If `g : M ⟶ X`,
  `f : X ⟶ Y` and `h : Y ⟶ Z` are morphisms, `X` and `Y` are indecomposable, and the image of
  `g ≫ f ≫ h` is nonzero, of finite length, and at least as long as the images of `g` and `h`,
  then `f` is an isomorphism.
* `TauCeti.length_image_map_le`: the length bound. For a chain of non-isomorphisms between
  indecomposable objects of length at most `b`, the composite of at least `2 ^ n - 1` links has
  image of length at most `b - n`.
* `TauCeti.map_eq_zero_of_length_le`: **the Harada–Sai lemma**, the case `n = b` of the bound.
* `TauCeti.ofSequence_map_eq_zero_of_length_le`: the same statement for a sequence of morphisms,
  and `TauCeti.map_op_eq_zero_of_length_le` for a descending chain.
* `CategoryTheory.ComposableArrows.hom_eq_zero_of_length_le`: the same statement for a finite
  chain `F : ComposableArrows C n`, continued by zero morphisms to a sequence.
* `TauCeti.jacobsonRadicalIdeal_pow_eq_bot_of_length_le`: in a Krull-Schmidt abelian category whose
  indecomposable objects have length at most `b`, the `(2 ^ b - 1)`-th power of the radical
  vanishes. The bound forces every indecomposable object to have finite length; when every object
  has finite length, it says that the radical is nilpotent.

## Implementation notes

The proof is the classical induction on `n` ([ARS, Lemma VI.1.2], [ASS, Lemma IV.5.2]). Write
the composite of `2 ^ (n + 1) - 1` links as `g ≫ f ≫ h`, with `g` and `h` composites of
`2 ^ n - 1` links. The bound for `n` on `g` and `h` and the failure of the bound for `n + 1` force
the images of `g`, `h` and `g ≫ f ≫ h` to have the same length. Then `f` induces an isomorphism
`θ` from the image `U` of `g` onto the image of `h`, so the inclusion of `U` into `X` and its
composite with `f` are both split monomorphisms into indecomposable objects
(`TauCeti.isIso_of_isIso_comp`); hence both are isomorphisms, and so is `f`. The classical proofs
are written for modules; the argument uses only images and the additivity of length on short exact
sequences (`CategoryTheory.length_eq_add_of_shortExact`).

The radical bound combines the lemma with the description of the powers of the radical of a
Krull-Schmidt category by chains of non-isomorphisms
(`TauCeti.jacobsonRadicalIdeal_pow_eq_bot_iff`).

## References

* M. Harada and Y. Sai, *On categories of indecomposable modules. I*, Osaka J. Math. 7 (1970),
  323–344, Lemma 12, where some composite of such a chain is shown to vanish.
* [ARS] M. Auslander, I. Reiten and S. O. Smalø, *Representation theory of Artin algebras*,
  Lemma VI.1.2 and Corollary VI.1.3.
* [ASS] I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of
  Associative Algebras, Vol. 1*, Lemma IV.5.2.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

section Step

variable {M X Y Z : C}

/-- **The Harada–Sai step.** Let `g : M ⟶ X`, `f : X ⟶ Y` and `h : Y ⟶ Z` be morphisms in an
abelian category, with `X` and `Y` indecomposable. If the image of `g ≫ f ≫ h` is nonzero, has
finite length, and is at least as long as the images of `g` and of `h`, then `f` is an
isomorphism. -/
theorem isIso_of_length_image_le_length_image_comp
    (hX : Indecomposable X) (hY : Indecomposable Y) {g : M ⟶ X} {f : X ⟶ Y} {h : Y ⟶ Z}
    (hne : ¬ IsZero (image (g ≫ f ≫ h))) (hfin : length (image (g ≫ f ≫ h)) ≠ ⊤)
    (hg : length (image g) ≤ length (image (g ≫ f ≫ h)))
    (hh : length (image h) ≤ length (image (g ≫ f ≫ h))) :
    IsIso f := by
  -- `f` induces `θ` from the image of `g` to the image of `h`, whose image is that of the
  -- composite; comparing lengths, `θ` is an isomorphism.
  set θ := image.ι g ≫ f ≫ factorThruImage h with hθ
  have hV : length (image (g ≫ f ≫ h)) = length (image θ) :=
    length_image_eq_of_fac (e := factorThruImage g ≫ factorThruImage θ)
      (m := image.ι θ ≫ image.ι h) (by simp [θ])
  have hU := le_antisymm (length_image_le_left θ) (hg.trans hV.le)
  have hW := le_antisymm (length_image_le_right θ) (hh.trans hV.le)
  have := mono_of_length_image_eq θ hU (hU ▸ hV ▸ hfin)
  have := epi_of_length_image_eq θ hW (hW ▸ hV ▸ hfin)
  have := isIso_of_mono_of_epi θ
  -- The inclusion of the image of `g` and its composite with `f` split through `θ⁻¹`.
  have hθinv : image.ι g ≫ f ≫ factorThruImage h ≫ inv θ = 𝟙 _ := by
    simpa only [hθ, Category.assoc] using IsIso.hom_inv_id θ
  have hUne : 𝟙 (image g) ≠ 0 := fun h0 ↦ hne (length_eq_zero_iff.mp
    (hV.trans (hU.trans (length_eq_zero_iff.mpr ((IsZero.iff_id_eq_zero _).mpr h0)))))
  have := isIso_of_isIso_comp hUne (fun _ he ↦ idempotent_eq_zero_or_id_of_indecomposable hX he)
    (image.ι g) (f ≫ factorThruImage h ≫ inv θ) (by rw [hθinv]; infer_instance)
  have := isIso_of_isIso_comp hUne (fun _ he ↦ idempotent_eq_zero_or_id_of_indecomposable hY he)
    (image.ι g ≫ f) (factorThruImage h ≫ inv θ) (by rw [Category.assoc, hθinv]; infer_instance)
  exact IsIso.of_isIso_comp_left (image.ι g) f

end Step

section Chain

variable {b : ℕ}

/-- **The Harada–Sai bound.** Let `F : ℕ ⥤ C` be a chain in an abelian category, whose links
`F.obj i ⟶ F.obj (i + 1)` are not isomorphisms, between indecomposable objects of length at most
`b`. Then the composite `F.obj i ⟶ F.obj j` of at least `2 ^ n - 1`
links has image of length at most `b - n`. -/
theorem length_image_map_le {F : ℕ ⥤ C} (hF : ∀ i, Indecomposable (F.obj i))
    (hlen : ∀ i, length (F.obj i) ≤ b)
    (hf : ∀ i, ¬ IsIso (F.map (homOfLE (Nat.le_add_right i 1)))) (n : ℕ) {i j : ℕ} (φ : i ⟶ j)
    (hij : i + (2 ^ n - 1) ≤ j) :
    length (image (F.map φ)) ≤ (b - n : ℕ) := by
  have himage {i j : ℕ} (φ : i ⟶ j) : length (image (F.map φ)) ≤ b :=
    (length_image_le_right _).trans (hlen j)
  induction n generalizing i j with
  | zero => simpa using himage φ
  | succ n ih =>
    have hpos := Nat.one_le_two_pow (n := n)
    by_cases hbn : b ≤ n
    · exact (ih φ (by omega)).trans (Nat.cast_le.mpr (by omega))
    -- Split the composite as `g`, then the link at `a`, then `h`, with `g` and `h` composites of
    -- `2 ^ n - 1` links, and argue by contradiction that the link at `a` is an isomorphism.
    set a := i + (2 ^ n - 1)
    have hφ : F.map φ = F.map (homOfLE (Nat.le_add_right i _ : i ≤ a)) ≫
        F.map (homOfLE (Nat.le_add_right a 1)) ≫ F.map (homOfLE (by omega : a + 1 ≤ j)) := by
      simp only [← Functor.map_comp]
      congr 1
    by_contra hcon
    have hc : ((b - n : ℕ) : ℕ∞) ≤ length (image (F.map φ)) := by
      have hsucc : b - n = b - (n + 1) + 1 := by omega
      rw [hsucc, Nat.cast_add, Nat.cast_one]
      exact Order.add_one_le_of_lt (not_le.mp hcon)
    have hg := ih (homOfLE (Nat.le_add_right i (2 ^ n - 1))) le_rfl
    have hh := ih (homOfLE (by omega : a + 1 ≤ j)) (by omega)
    have hfin := (himage φ).trans_lt (WithTop.coe_lt_top b)
    rw [hφ] at hc hfin
    refine hf a (isIso_of_length_image_le_length_image_comp (hF a) (hF (a + 1)) ?_ hfin.ne
      (hg.trans hc) (hh.trans hc))
    intro hzero
    rw [length_eq_zero_iff.mpr hzero] at hc
    have : b - n ≤ 0 := by exact_mod_cast hc
    omega

/-- **The Harada–Sai lemma.** Let `F : ℕ ⥤ C` be a chain in an abelian category, whose links
`F.obj i ⟶ F.obj (i + 1)` are not isomorphisms, between indecomposable objects of length at most
`b`. Then every composite `F.obj i ⟶ F.obj j` of at least `2 ^ b - 1`
links is zero. -/
theorem map_eq_zero_of_length_le {F : ℕ ⥤ C} (hF : ∀ i, Indecomposable (F.obj i))
    (hlen : ∀ i, length (F.obj i) ≤ b)
    (hf : ∀ i, ¬ IsIso (F.map (homOfLE (Nat.le_add_right i 1)))) {i j : ℕ} (φ : i ⟶ j)
    (hij : i + (2 ^ b - 1) ≤ j) : F.map φ = 0 := by
  have h := length_image_map_le hF hlen hf b φ hij
  rw [Nat.sub_self, Nat.cast_zero, nonpos_iff_eq_zero] at h
  exact eq_zero_of_length_image_eq_zero _ h

/-- **The Harada–Sai lemma**, for a sequence of morphisms `f i : X i ⟶ X (i + 1)` that are not
isomorphisms, between indecomposable objects of length at most `b`: the composite `X 0 ⟶ X n` of
the first `n` of them is zero once `n ≥ 2 ^ b - 1`. -/
theorem ofSequence_map_eq_zero_of_length_le {X : ℕ → C} (f : ∀ i, X i ⟶ X (i + 1))
    (hX : ∀ i, Indecomposable (X i)) (hlen : ∀ i, length (X i) ≤ b) (hf : ∀ i, ¬ IsIso (f i))
    {n : ℕ} (hn : 2 ^ b - 1 ≤ n) : (Functor.ofSequence f).map (homOfLE (Nat.zero_le n)) = 0 :=
  map_eq_zero_of_length_le hX hlen
    (fun i ↦ by rw [Functor.ofSequence_map_homOfLE_succ]; exact hf i) _ (by omega)

open Opposite in
/-- **The Harada–Sai lemma for descending chains.** Let `G : ℕᵒᵖ ⥤ C` be a descending chain in an
abelian category, whose links `G.obj (op (i + 1)) ⟶ G.obj (op i)` are not isomorphisms, between
indecomposable objects of length at most `b`. Then every composite
`G.obj (op j) ⟶ G.obj (op i)` of at least `2 ^ b - 1` links is zero. -/
theorem map_op_eq_zero_of_length_le {G : ℕᵒᵖ ⥤ C}
    (hG : ∀ i, Indecomposable (G.obj (op i))) (hlen : ∀ i, length (G.obj (op i)) ≤ b)
    (hf : ∀ i, ¬ IsIso (G.map (homOfLE (Nat.le_add_right i 1)).op)) {i j : ℕ} (φ : i ⟶ j)
    (hij : i + (2 ^ b - 1) ≤ j) : G.map φ.op = 0 := by
  classical
  -- Read the first `j` links backwards, continued by zero morphisms.
  let g (k : ℕ) : G.obj (op (j - k)) ⟶ G.obj (op (j - (k + 1))) :=
    if k < j then G.map (homOfLE (by omega : j - (k + 1) ≤ j - k)).op else 0
  have hlink (k m : ℕ) (h : k ≤ m) (hm : m = k + 1) : ¬ IsIso (G.map (homOfLE h).op) := by
    subst hm
    exact hf k
  have hg (k : ℕ) : ¬ IsIso (g k) := by
    by_cases hk : k < j
    · simp only [g, hk, ↓reduceIte]
      exact hlink (j - (k + 1)) (j - k) _ (by omega)
    · simp only [g, hk, ↓reduceIte]
      intro h
      exact (hG (j - k)).1 ((IsZero.iff_id_eq_zero _).mpr
        ((IsIso.hom_inv_id (0 : G.obj (op (j - k)) ⟶ G.obj (op (j - (k + 1))))).symm.trans
          zero_comp))
  have hcomp (m : ℕ) (hm : m ≤ j) : (Functor.ofSequence g).map (homOfLE (Nat.zero_le m)) =
      G.map (homOfLE (by omega : j - m ≤ j)).op := by
    induction m with
    -- `(Functor.ofSequence g).obj m` is `G.obj (op (j - m))` by definition.
    | zero => simp
    | succ m ih =>
      have hmj : m < j := by omega
      rw [← homOfLE_comp (Nat.zero_le m) (Nat.le_succ m), Functor.map_comp, ih (by omega),
        Functor.ofSequence_map_homOfLE_succ]
      simp only [g, hmj, ↓reduceIte]
      exact (G.map_comp _ _).symm
  have h0 := ofSequence_map_eq_zero_of_length_le g (fun k ↦ hG _) (fun k ↦ hlen _) hg
    (by omega : 2 ^ b - 1 ≤ j - i)
  rw [hcomp (j - i) (by omega)] at h0
  -- The composite of the first `j - i` links read backwards ends at `j - (j - i) = i`.
  have key (m : ℕ) (h : m ≤ j) (hm : m = i) (h' : G.map (homOfLE h).op = 0) :
      G.map φ.op = 0 := by
    subst hm
    rwa [Subsingleton.elim φ (homOfLE h)]
  exact key _ _ (by omega) h0

end Chain

end TauCeti

namespace CategoryTheory.ComposableArrows

open TauCeti Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **The Harada–Sai lemma for a finite chain.** Let `F` be a chain
`F.obj 0 ⟶ F.obj 1 ⟶ ⋯ ⟶ F.obj n` of `n` morphisms that are not isomorphisms, between
indecomposable objects of length at most `b` in an abelian category. If `n ≥ 2 ^ b - 1`, its
composite `F.hom` is zero. -/
theorem hom_eq_zero_of_length_le {b n : ℕ} (F : ComposableArrows C n)
    (hF : ∀ i, Indecomposable (F.obj i)) (hlen : ∀ i, length (F.obj i) ≤ b)
    (hf : ∀ (i : ℕ) (hi : i < n), ¬ IsIso (F.map' i (i + 1))) (hn : 2 ^ b - 1 ≤ n) :
    F.hom = 0 := by
  classical
  -- Continue the chain by zero endomorphisms of its last object.
  let g (i : ℕ) : F.obj ⟨min i n, by omega⟩ ⟶ F.obj ⟨min (i + 1) n, by omega⟩ :=
    if i < n then F.map (homOfLE (by simp only [Fin.mk_le_mk]; omega)) else 0
  -- A statement about a morphism of `F` transfers along equalities of its endpoints.
  have key {a c a' c' : Fin (n + 1)} (h : a ≤ c) (h' : a' ≤ c') (ha : a = a') (hc : c = c')
      (P : ∀ {X Y : C}, (X ⟶ Y) → Prop) :
      P (F.map (homOfLE h)) ↔ P (F.map (homOfLE h')) := by
    subst ha hc
    rfl
  have hg (i : ℕ) : ¬ IsIso (g i) := by
    by_cases hi : i < n
    · simp only [g, hi, ↓reduceIte]
      exact fun hiso ↦ hf i hi ((key _ _ (Fin.ext (Nat.min_eq_left hi.le))
        (Fin.ext (Nat.min_eq_left hi)) fun φ ↦ IsIso φ).mp hiso)
    · simp only [g, hi, ↓reduceIte]
      intro h
      exact (hF _).1 ((IsZero.iff_id_eq_zero _).mpr
        ((IsIso.hom_inv_id (0 : F.obj ⟨min i n, _⟩ ⟶ F.obj ⟨min (i + 1) n, _⟩)).symm.trans
          zero_comp))
  have hcomp (m : ℕ) (hm : m ≤ n) : (Functor.ofSequence g).map (homOfLE (Nat.zero_le m)) =
      F.map (homOfLE (by simp only [Fin.mk_le_mk]; omega) :
        (⟨min 0 n, by omega⟩ : Fin (n + 1)) ⟶ ⟨min m n, by omega⟩) := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hmn : m < n := by omega
      rw [← homOfLE_comp (Nat.zero_le m) (Nat.le_succ m), Functor.map_comp, ih (by omega),
        Functor.ofSequence_map_homOfLE_succ]
      simp only [g, hmn, ↓reduceIte]
      exact (F.map_comp _ _).symm
  have h0 := ofSequence_map_eq_zero_of_length_le g (fun i ↦ hF _) (fun i ↦ hlen _) hg hn
  rw [hcomp n le_rfl] at h0
  exact (key _ _ (Fin.ext (Nat.zero_min n)) (Fin.ext (min_self n)) fun φ ↦ φ = 0).mp h0

end CategoryTheory.ComposableArrows

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **The radical of a Krull-Schmidt abelian category is nilpotent of index at most `2 ^ b - 1`**
when every indecomposable object has length at most `b`: the `(2 ^ b - 1)`-th power of the radical
vanishes. -/
theorem jacobsonRadicalIdeal_pow_eq_bot_of_length_le [HasFiniteBiproducts C] [IsKrullSchmidt C]
    {b : ℕ} (h : ∀ X : C, Indecomposable X → length X ≤ b) :
    jacobsonRadicalIdeal C ^ (2 ^ b - 1) = ⊥ := by
  refine (jacobsonRadicalIdeal_pow_eq_bot_iff _).mpr fun G hG hl ↦ ?_
  have hind (i : Fin (2 ^ b - 1 + 1)) : Indecomposable (G.obj i) :=
    indecomposable_of_isLocalRing_end
  exact G.hom_eq_zero_of_length_le hind (fun i ↦ h _ (hind i)) hl le_rfl

end TauCeti
