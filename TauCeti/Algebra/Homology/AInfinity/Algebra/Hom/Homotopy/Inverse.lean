/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.BarDifferential
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Transformation

/-!
# Lifting chain-homotopy inverses to A-infinity homotopy inverses

Let `f : A ⟶ B` be a morphism of `A∞` algebras over a commutative ring `R`.  Taking arity-one
components of any two-sided `A∞` homotopy inverse of `f` produces a graded chain-homotopy inverse
to `f.linearPart` between the unary complexes `(A, m₁)` and `(B, m₁)`, packaged here as
`TauCeti.AInfinityHom.LinearHomotopyInverse`.

Conversely, this file lifts every `d : f.LinearHomotopyInverse` to an `A∞` morphism
`d.homotopyInverse : B ⟶ A` together with `A∞` homotopies
`d.leftHomotopyLift : d.homotopyInverse ∘ f ⇒ id_A` and
`d.rightHomotopyLift : f ∘ d.homotopyInverse ⇒ id_B`.  No projectivity, cofibrancy, or field
assumption is needed beyond `d` itself:

1. **Vogt rectification.**  Replacing the right chain homotopy `k_B` by
   `k_B' = k_B + f₁ (k_A g₁ - g₁ k_B)` preserves the chain-homotopy equation
   `f₁ g₁ - 1 = m₁ k_B' + k_B' m₁` and promotes `(f₁, g₁, k_A, k_B')` to an adjoint chain
   homotopy equivalence witnessed by `m = f₁ k_A² - k_B f₁ k_A + k_B² f₁`, which satisfies
   `m₁ m - m m₁ = f₁ k_A - k_B' f₁`.
2. **Stage 1: lifting the right homotopy inverse.**  Along the tensor-length filtration of
   `Tᶜ(sB)`, we simultaneously extend `g₁` to Taylor components `γₙ` of a coalgebra morphism `Gₙ`
   and `k_B'` to Taylor components `ηₙ` of an `(F ∘ Gₙ, 1)`-coderivation `Hₙ`.  When the morphism
   defect `E_G = b_A Gₙ - Gₙ b_B` and the homotopy defect `E_H = (F Gₙ - 1) - (b_B Hₙ + Hₙ b_B)`
   vanish on words of length at most `n`, both send a word of length `n + 1` to a single letter,
   and the identities `b_A E_G + E_G b_B = 0` and `b_B E_H - E_H b_B = F E_G` reduce on length
   `n + 1` to `Φ b_B^{unary} = -m₁ Φ` and `Ψ b_B^{unary} = m₁ Ψ - f₁ Φ`.  The explicit
   corrections `δγ = -g₁ Ψ + k_A Φ` and `δη = -k_B' Ψ + m Φ` kill both defects on words of length
   `n + 1` without altering lower arities; passing to the stabilising limit yields `g : B ⟶ A` and
   `h_R : f ∘ g ⇒ id_B`.
3. **Stage 2: lifting the left homotopy.**  With `g` and `h_R` fixed, we lift `k_A` and `-m` along
   the tensor-length filtration of `Tᶜ(sA)` to a `(G ∘ F, 1)`-coderivation `Lₙ` of degree `-1` and
   an `(F ∘ G ∘ F, F)`-coderivation `Mₙ` of degree `-2` killing both
   `E_L = (G F - 1) - (b_A Lₙ + Lₙ b_A)` and `E_M = (H_R F - F Lₙ) - (b_B Mₙ - Mₙ b_A)`.  Their
   length-`(n + 1)` components `Θ` and `Ξ` satisfy `Θ b_A^{unary} = m₁ Θ` and
   `Ξ b_A^{unary} = f₁ Θ - m₁ Ξ`, and the corrections `δθ = g₁ Ξ - k_A Θ` and
   `δμ = -k_B' Ξ + m Θ` kill both, assembling in the limit to `h_L : g ∘ f ⇒ id_A`.

## Main definitions

* `TauCeti.AInfinityHom.LinearHomotopyInverse`: a graded chain-homotopy inverse to `f.linearPart`.
* `TauCeti.AInfinityHom.Homotopy.toLinearHomotopyInverse`: the linear chain-homotopy inverse
  extracted from two-sided `A∞` homotopies.
* `TauCeti.AInfinityHom.LinearHomotopyInverse.homotopyInverse`,
  `TauCeti.AInfinityHom.LinearHomotopyInverse.leftHomotopyLift`, and
  `TauCeti.AInfinityHom.LinearHomotopyInverse.rightHomotopyLift`: the lifted `A∞` morphism and its
  left and right `A∞` homotopies.

## Main results

* `TauCeti.AInfinityHom.LinearHomotopyInverse.linearPart_homotopyInverse`,
  `TauCeti.AInfinityHom.LinearHomotopyInverse.linearHomotopy_leftHomotopyLift`, and
  `TauCeti.AInfinityHom.LinearHomotopyInverse.linearHomotopy_rightHomotopyLift`: arity-one
  components of the lifted `A∞` inverse and homotopies.

## References

* A. Prouté, *`A∞`-structures: Modèle minimal de Baues–Lemaire et homologie des fibrations*,
  Reprints in Theory and Applications of Categories 21 (2011), 1--99 (thèse d'État, 1986), §4.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, thèse de doctorat, Université Paris 7
  (2003), Theorem 1.3.3.1.
* M. Markl, *Transferring `A∞` (strongly homotopy associative) structures*, Rend. Circ. Mat.
  Palermo Suppl. 79 (2006), 139--151.
* R. M. Vogt, *Convenient categories of topological spaces and homotopy theory*, Arch. Math. 24
  (1973), Lemma 2.
-/

public section

namespace TauCeti

open ReducedTensorWords

universe uR uA uB uC

section FiltrationHelpers

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

/-- The letter projection kills every component except length one, so it absorbs `lengthProj 1`. -/
private theorem letter_comp_lengthProj_one :
    letter R A ∘ₗ lengthProj R A ⟨1, Nat.one_pos⟩ = letter R A := by
  refine linearMap_ext R A fun m x ↦ ?_
  by_cases hm : m = ⟨1, Nat.one_pos⟩
  · subst hm
    rw [LinearMap.comp_apply, lengthProj_of_self]
  · rw [LinearMap.comp_apply, lengthProj_of_of_ne R A hm, letter_of_of_ne_one R A hm, map_zero]

/-- Two linear maps agreeing on single letters agree on `filtration 1`. -/
private theorem eq_of_mem_filtration_one {N : Type*} [AddCommGroup N] [Module R N]
    (f g : ReducedTensorWords R A →ₗ[R] N) (h : ∀ a, f (ofLetter R A a) = g (ofLetter R A a))
    {z : ReducedTensorWords R A} (hz : z ∈ filtration R A 1) : f z = g z := by
  have hfg : (f - g : ReducedTensorWords R A →ₗ[R] N) ∘ₗ ofLetter R A = 0 :=
    LinearMap.ext fun a ↦ by
      rw [LinearMap.comp_apply, LinearMap.sub_apply, h a, sub_self, LinearMap.zero_apply]
  exact sub_eq_zero.1 (apply_eq_zero_of_mem_filtration_one R A hfg z hz)

/-- The unary bar differential preserves word length, so it commutes with `lengthProj`. -/
private theorem lengthProj_comp_unaryBarDifferential (𝒜 : AInfinityAlgebra R A)
    (n : {n : ℕ // 0 < n}) :
    lengthProj R A n ∘ₗ 𝒜.unaryBarDifferential = 𝒜.unaryBarDifferential ∘ₗ lengthProj R A n := by
  rw [𝒜.unaryBarDifferential_eq_gradedCoderiv]
  refine lengthProj_comp_gradedCoderiv (𝒜.grading.shift 1) 1 (a := ⟨1, Nat.one_pos⟩) ?_ rfl
  rw [LinearMap.comp_assoc, letter_comp_lengthProj_one]

/-- A linear map vanishing on `filtration n` sees `barDifferential` on `filtration (n + 1)` solely
through `unaryBarDifferential`, since `higherBarDifferential` strictly lowers word length. -/
private theorem apply_barDifferential_eq_unary_of_mem_filtration (𝒜 : AInfinityAlgebra R A)
    (X : ReducedTensorWords R A →ₗ[R] B) {n : ℕ} (hX : ∀ w ∈ filtration R A n, X w = 0)
    {z : ReducedTensorWords R A} (hz : z ∈ filtration R A (n + 1)) :
    X (𝒜.barDifferential z) = X (𝒜.unaryBarDifferential z) := by
  rw [𝒜.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add,
    hX _ (𝒜.higherBarDifferential_filtration n ⟨z, hz, rfl⟩), add_zero]

/-- If `E` vanishes on `filtration n` and satisfies the untwisted co-Leibniz rule along `(F, F')`
at a word `z` of length at most `n + 1`, then `E z` is the single letter given by `letter (E z)`. -/
private theorem eq_ofLetter_of_deconcatenation_eq_of_mem_filtration
    {E F F' : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B} {n : ℕ}
    (hE : ∀ w ∈ filtration R A n, E w = 0) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A (n + 1))
    (hΔ : deconcatenation R B (E z) =
      TensorProduct.map E F' (deconcatenation R A z) +
        TensorProduct.map F E (deconcatenation R A z)) :
    E z = ofLetter R B (letter R B (E z)) := by
  refine eq_of_deconcatenation_eq_of_letter_eq R B ?_ (letter_ofLetter R B _).symm
  rw [deconcatenation_ofLetter, hΔ,
    map_deconcatenation_eq_zero_of_mem_filtration R A hE
      (apply_eq_zero_of_mem_filtration_zero R A F') hz,
    map_deconcatenation_eq_zero_of_mem_filtration R A
      (apply_eq_zero_of_mem_filtration_zero R A F) hE (by rwa [zero_add]), add_zero]

/-- Limit of a sequence of Taylor maps `φ m` that stabilise on `filtration (m + 1)`: on words of
length `k` it evaluates `φ (k - 1)`. -/
private noncomputable def stabilisingTaylor (φ : ℕ → ReducedTensorWords R A →ₗ[R] B) :
    ReducedTensorWords R A →ₗ[R] B :=
  DirectSum.toModule R _ _ fun k ↦ φ (k.1 - 1) ∘ₗ of R A k

private theorem stabilisingTaylor_apply_eq_of_le {φ : ℕ → ReducedTensorWords R A →ₗ[R] B}
    (hφ : ∀ m, ∀ z ∈ filtration R A (m + 1), φ (m + 1) z = φ m z) {j m : ℕ} (hjm : j ≤ m)
    {z : ReducedTensorWords R A} (hz : z ∈ filtration R A (j + 1)) :
    φ m z = φ j z := by
  induction m, hjm using Nat.le_induction with
  | base => rfl
  | succ m hjm ih => rw [hφ m z (filtration_monotone R A (Nat.succ_le_succ hjm) hz), ih]

/-- On words of length at most `m + 1`, `stabilisingTaylor φ` agrees with `φ m`. -/
private theorem stabilisingTaylor_apply_of_mem_filtration {φ : ℕ → ReducedTensorWords R A →ₗ[R] B}
    (hφ : ∀ m, ∀ z ∈ filtration R A (m + 1), φ (m + 1) z = φ m z) {m : ℕ}
    {z : ReducedTensorWords R A} (hz : z ∈ filtration R A (m + 1)) :
    stabilisingTaylor φ z = φ m z := by
  have h : filtration R A (m + 1) ≤ LinearMap.eqLocus (stabilisingTaylor φ) (φ m) := by
    rw [filtration_le_iff]
    rintro k hk _ ⟨x, rfl⟩
    have hk1 : (k.1 - 1) + 1 = k.1 := by have := k.2; omega
    rw [LinearMap.mem_eqLocus, stabilisingTaylor, toModule_of, LinearMap.comp_apply,
      stabilisingTaylor_apply_eq_of_le hφ (by omega : k.1 - 1 ≤ m)
        (hk1.symm ▸ of_mem_filtration R A le_rfl x)]
  exact h hz

/-- If every `φ m` is homogeneous of degree `p`, then `stabilisingTaylor φ` is homogeneous of
degree `p`. -/
private theorem isHomogeneous_stabilisingTaylor {G : InternalGrading R A ℤ}
    {H : InternalGrading R B ℤ} {p : ℤ} {φ : ℕ → ReducedTensorWords R A →ₗ[R] B}
    (hφ : ∀ m, ∀ z ∈ filtration R A (m + 1), φ (m + 1) z = φ m z)
    (hhom : ∀ m, LinearMap.IsHomogeneous (φ m) (gradedPiece G) H.piece p) :
    LinearMap.IsHomogeneous (stabilisingTaylor φ) (gradedPiece G) H.piece p := by
  rw [LinearMap.isHomogeneous_def]
  intro q z hz
  obtain ⟨m, hm⟩ := exists_mem_filtration R A z
  rw [stabilisingTaylor_apply_of_mem_filtration hφ (filtration_monotone R A m.le_succ hm)]
  exact (hhom m).map_mem hz

private theorem isHomogeneous_comp_of_eq {M₁ M₂ M₃ σ₁ σ₂ σ₃ : Type*}
    [AddCommMonoid M₁] [Module R M₁] [SetLike σ₁ M₁]
    [AddCommMonoid M₂] [Module R M₂] [SetLike σ₂ M₂]
    [AddCommMonoid M₃] [Module R M₃] [SetLike σ₃ M₃]
    {P₁ : ℤ → σ₁} {P₂ : ℤ → σ₂} {P₃ : ℤ → σ₃}
    {g : M₂ →ₗ[R] M₃} {f : M₁ →ₗ[R] M₂} {q r s : ℤ}
    (hg : LinearMap.IsHomogeneous g P₂ P₃ r) (hf : LinearMap.IsHomogeneous f P₁ P₂ q)
    (h : q + r = s := by rfl) : LinearMap.IsHomogeneous (g ∘ₗ f) P₁ P₃ s :=
  h ▸ hg.comp hf

end FiltrationHelpers

namespace AInfinityHom

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-- The linear part of an `A∞` morphism intertwines the unary differentials. -/
theorem differential_comp_linearPart (f : AInfinityHom AA BB) :
    BB.differential ∘ₗ f.linearPart = f.linearPart ∘ₗ AA.differential :=
  LinearMap.ext fun a ↦ by
    simp only [LinearMap.comp_apply, AInfinityAlgebra.differential_apply, f.linearPart_m_one]

/-- The linear component of an `A∞` homotopy has internal degree `-1`. -/
theorem Homotopy.isHomogeneous_linearHomotopy {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    LinearMap.IsHomogeneous h.linearHomotopy AA.grading.piece BB.grading.piece (-1) :=
  LinearMap.isHomogeneous_def.2 fun _ _ ha ↦ by
    rw [← sub_eq_add_neg]; exact h.linearHomotopy_mem ha

/-! ### Linear chain-homotopy inverses and Vogt rectification -/

/-- A graded **chain-homotopy inverse** to the linear part `f₁` of an `A∞` morphism `f : A ⟶ B`:
a degree-zero chain map `inv : B →ₗ[R] A` for the unary differentials together with degree-`-1`
chain homotopies `leftHomotopy` and `rightHomotopy` witnessing `inv ∘ f₁ - id = m₁ h_L + h_L m₁`
and `f₁ ∘ inv - id = m₁ h_R + h_R m₁`. -/
structure LinearHomotopyInverse (f : AInfinityHom AA BB) where
  /-- The inverse chain map on the underlying graded modules. -/
  inv : B →ₗ[R] A
  /-- The inverse chain map preserves internal degrees. -/
  isHomogeneous_inv : LinearMap.IsHomogeneous inv BB.grading.piece AA.grading.piece 0
  /-- The inverse chain map intertwines the unary differentials. -/
  differential_comp_inv : AA.differential ∘ₗ inv = inv ∘ₗ BB.differential
  /-- The left chain homotopy witnessing `inv ∘ f₁ ≃ id_A`. -/
  leftHomotopy : A →ₗ[R] A
  /-- The left chain homotopy has internal degree `-1`. -/
  isHomogeneous_leftHomotopy :
    LinearMap.IsHomogeneous leftHomotopy AA.grading.piece AA.grading.piece (-1)
  /-- The left chain-homotopy equation `inv ∘ f₁ - id = d_A ∘ h_L + h_L ∘ d_A`. -/
  inv_comp_linearPart_sub_id :
    inv ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ leftHomotopy + leftHomotopy ∘ₗ AA.differential
  /-- The right chain homotopy witnessing `f₁ ∘ inv ≃ id_B`. -/
  rightHomotopy : B →ₗ[R] B
  /-- The right chain homotopy has internal degree `-1`. -/
  isHomogeneous_rightHomotopy :
    LinearMap.IsHomogeneous rightHomotopy BB.grading.piece BB.grading.piece (-1)
  /-- The right chain-homotopy equation `f₁ ∘ inv - id = d_B ∘ h_R + h_R ∘ d_B`. -/
  linearPart_comp_inv_sub_id :
    f.linearPart ∘ₗ inv - LinearMap.id =
      BB.differential ∘ₗ rightHomotopy + rightHomotopy ∘ₗ BB.differential

/-- Arity-one components of two-sided `A∞` homotopies form a `LinearHomotopyInverse`. -/
noncomputable def Homotopy.toLinearHomotopyInverse {f : AInfinityHom AA BB}
    {g : AInfinityHom BB AA} (hL : Homotopy (g.comp f) (AInfinityHom.id AA))
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) : f.LinearHomotopyInverse where
  inv := g.linearPart
  isHomogeneous_inv := g.isHomogeneous_linearPart
  differential_comp_inv := g.differential_comp_linearPart
  leftHomotopy := hL.linearHomotopy
  isHomogeneous_leftHomotopy := hL.isHomogeneous_linearHomotopy
  inv_comp_linearPart_sub_id := LinearMap.ext fun a ↦ by
    simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      linearPart_comp, linearPart_id, AInfinityAlgebra.differential_apply] using
      hL.linearPart_sub_linearPart a
  rightHomotopy := hR.linearHomotopy
  isHomogeneous_rightHomotopy := hR.isHomogeneous_linearHomotopy
  linearPart_comp_inv_sub_id := LinearMap.ext fun b ↦ by
    simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      linearPart_comp, linearPart_id, AInfinityAlgebra.differential_apply] using
      hR.linearPart_sub_linearPart b

namespace LinearHomotopyInverse

private theorem differential_inv_apply {f : AInfinityHom AA BB} (d : f.LinearHomotopyInverse)
    (b : B) : AA.differential (d.inv b) = d.inv (BB.differential b) :=
  LinearMap.congr_fun d.differential_comp_inv b

private theorem differential_leftHomotopy_apply {f : AInfinityHom AA BB}
    (d : f.LinearHomotopyInverse) (a : A) :
    AA.differential (d.leftHomotopy a) =
      d.inv (f.linearPart a) - a - d.leftHomotopy (AA.differential a) :=
  eq_sub_of_add_eq (LinearMap.congr_fun d.inv_comp_linearPart_sub_id a).symm

private theorem differential_rightHomotopy_apply {f : AInfinityHom AA BB}
    (d : f.LinearHomotopyInverse) (b : B) :
    BB.differential (d.rightHomotopy b) =
      f.linearPart (d.inv b) - b - d.rightHomotopy (BB.differential b) :=
  eq_sub_of_add_eq (LinearMap.congr_fun d.linearPart_comp_inv_sub_id b).symm

/-- The identity chain-homotopy inverse of the identity `A∞` morphism. -/
def id (AA : AInfinityAlgebra R A) : (AInfinityHom.id AA).LinearHomotopyInverse where
  inv := LinearMap.id
  isHomogeneous_inv := LinearMap.isHomogeneous_id _
  differential_comp_inv := by rw [LinearMap.comp_id, LinearMap.id_comp]
  leftHomotopy := 0
  isHomogeneous_leftHomotopy := LinearMap.isHomogeneous_zero _ _ _
  inv_comp_linearPart_sub_id := by
    rw [linearPart_id, LinearMap.id_comp, sub_self, LinearMap.comp_zero, LinearMap.zero_comp,
      add_zero]
  rightHomotopy := 0
  isHomogeneous_rightHomotopy := LinearMap.isHomogeneous_zero _ _ _
  linearPart_comp_inv_sub_id := by
    rw [linearPart_id, LinearMap.comp_id, sub_self, LinearMap.comp_zero, LinearMap.zero_comp,
      add_zero]

/-- Composition of linear chain-homotopy inverses. -/
noncomputable def comp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (dg : g.LinearHomotopyInverse) (df : f.LinearHomotopyInverse) :
    (g.comp f).LinearHomotopyInverse where
  inv := df.inv ∘ₗ dg.inv
  isHomogeneous_inv := isHomogeneous_comp_of_eq df.isHomogeneous_inv dg.isHomogeneous_inv
  differential_comp_inv := LinearMap.ext fun c ↦ by
    simp only [LinearMap.comp_apply, df.differential_inv_apply, dg.differential_inv_apply]
  leftHomotopy := df.leftHomotopy + df.inv ∘ₗ dg.leftHomotopy ∘ₗ f.linearPart
  isHomogeneous_leftHomotopy := df.isHomogeneous_leftHomotopy.add <|
    isHomogeneous_comp_of_eq df.isHomogeneous_inv
      (isHomogeneous_comp_of_eq dg.isHomogeneous_leftHomotopy f.isHomogeneous_linearPart)
  inv_comp_linearPart_sub_id := LinearMap.ext fun a ↦ by
    have hf : BB.differential (f.linearPart a) = f.linearPart (AA.differential a) :=
      LinearMap.congr_fun f.differential_comp_linearPart a
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      linearPart_comp, map_add, df.differential_inv_apply, df.differential_leftHomotopy_apply,
      dg.differential_leftHomotopy_apply, ← hf, map_sub]
    abel
  rightHomotopy := dg.rightHomotopy + g.linearPart ∘ₗ df.rightHomotopy ∘ₗ dg.inv
  isHomogeneous_rightHomotopy := dg.isHomogeneous_rightHomotopy.add <|
    isHomogeneous_comp_of_eq g.isHomogeneous_linearPart
      (isHomogeneous_comp_of_eq df.isHomogeneous_rightHomotopy dg.isHomogeneous_inv)
  linearPart_comp_inv_sub_id := LinearMap.ext fun c ↦ by
    have hg : ∀ b, CC.differential (g.linearPart b) = g.linearPart (BB.differential b) :=
      LinearMap.congr_fun g.differential_comp_linearPart
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      linearPart_comp, map_add, hg, ← dg.differential_inv_apply,
      dg.differential_rightHomotopy_apply, df.differential_rightHomotopy_apply, map_sub]
    abel

/-- Transport a `LinearHomotopyInverse` forward along an `A∞` homotopy `f ⇒ f'`. -/
noncomputable def ofHomotopy {f f' : AInfinityHom AA BB} (d : f.LinearHomotopyInverse)
    (h : Homotopy f f') : f'.LinearHomotopyInverse where
  inv := d.inv
  isHomogeneous_inv := d.isHomogeneous_inv
  differential_comp_inv := d.differential_comp_inv
  leftHomotopy := d.leftHomotopy - d.inv ∘ₗ h.linearHomotopy
  isHomogeneous_leftHomotopy :=
    d.isHomogeneous_leftHomotopy.sub
      (isHomogeneous_comp_of_eq d.isHomogeneous_inv h.isHomogeneous_linearHomotopy)
  inv_comp_linearPart_sub_id := LinearMap.ext fun a ↦ by
    have hf' : f'.linearPart a = f.linearPart a -
        (BB.differential (h.linearHomotopy a) + h.linearHomotopy (AA.differential a)) := by
      rw [AInfinityAlgebra.differential_apply, AInfinityAlgebra.differential_apply,
        ← h.linearPart_sub_linearPart a, sub_sub_cancel]
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      hf', map_sub, map_add, d.differential_inv_apply, d.differential_leftHomotopy_apply]
    abel
  rightHomotopy := d.rightHomotopy - h.linearHomotopy ∘ₗ d.inv
  isHomogeneous_rightHomotopy :=
    d.isHomogeneous_rightHomotopy.sub
      (isHomogeneous_comp_of_eq h.isHomogeneous_linearHomotopy d.isHomogeneous_inv)
  linearPart_comp_inv_sub_id := LinearMap.ext fun b ↦ by
    have hf' : f'.linearPart (d.inv b) = f.linearPart (d.inv b) -
        (BB.differential (h.linearHomotopy (d.inv b)) +
          h.linearHomotopy (AA.differential (d.inv b))) := by
      rw [AInfinityAlgebra.differential_apply, AInfinityAlgebra.differential_apply,
        ← h.linearPart_sub_linearPart (d.inv b), sub_sub_cancel]
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      hf', map_sub, d.differential_inv_apply, d.differential_rightHomotopy_apply]
    abel

/-- Transport a `LinearHomotopyInverse` backward along an `A∞` homotopy `f ⇒ f'`. -/
noncomputable def ofHomotopySymm {f f' : AInfinityHom AA BB} (d : f'.LinearHomotopyInverse)
    (h : Homotopy f f') : f.LinearHomotopyInverse where
  inv := d.inv
  isHomogeneous_inv := d.isHomogeneous_inv
  differential_comp_inv := d.differential_comp_inv
  leftHomotopy := d.leftHomotopy + d.inv ∘ₗ h.linearHomotopy
  isHomogeneous_leftHomotopy :=
    d.isHomogeneous_leftHomotopy.add
      (isHomogeneous_comp_of_eq d.isHomogeneous_inv h.isHomogeneous_linearHomotopy)
  inv_comp_linearPart_sub_id := LinearMap.ext fun a ↦ by
    have hf : f.linearPart a =
        (BB.differential (h.linearHomotopy a) + h.linearHomotopy (AA.differential a)) +
          f'.linearPart a := by
      rw [AInfinityAlgebra.differential_apply, AInfinityAlgebra.differential_apply]
      exact eq_add_of_sub_eq (h.linearPart_sub_linearPart a)
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      hf, map_add, d.differential_inv_apply, d.differential_leftHomotopy_apply]
    abel
  rightHomotopy := d.rightHomotopy + h.linearHomotopy ∘ₗ d.inv
  isHomogeneous_rightHomotopy :=
    d.isHomogeneous_rightHomotopy.add
      (isHomogeneous_comp_of_eq h.isHomogeneous_linearHomotopy d.isHomogeneous_inv)
  linearPart_comp_inv_sub_id := LinearMap.ext fun b ↦ by
    have hf : f.linearPart (d.inv b) =
        (BB.differential (h.linearHomotopy (d.inv b)) +
          h.linearHomotopy (AA.differential (d.inv b))) + f'.linearPart (d.inv b) := by
      rw [AInfinityAlgebra.differential_apply, AInfinityAlgebra.differential_apply]
      exact eq_add_of_sub_eq (h.linearPart_sub_linearPart (d.inv b))
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      hf, map_add, d.differential_inv_apply, d.differential_rightHomotopy_apply]
    abel

section VogtRectification

variable {f : AInfinityHom AA BB} (d : f.LinearHomotopyInverse)

/-- Vogt's rectified right chain homotopy `k_B + f₁ (k_A g₁ - g₁ k_B)`, which still bounds
`f₁ g₁ - id_B` while becoming coherent with `k_A` modulo a degree-`-2` homotopy. -/
noncomputable def rectifiedRightHomotopy : B →ₗ[R] B :=
  d.rightHomotopy + f.linearPart ∘ₗ (d.leftHomotopy ∘ₗ d.inv - d.inv ∘ₗ d.rightHomotopy)

/-- The rectified right chain homotopy has internal degree `-1`. -/
theorem isHomogeneous_rectifiedRightHomotopy :
    LinearMap.IsHomogeneous d.rectifiedRightHomotopy BB.grading.piece BB.grading.piece (-1) :=
  d.isHomogeneous_rightHomotopy.add <|
    isHomogeneous_comp_of_eq f.isHomogeneous_linearPart <|
      LinearMap.IsHomogeneous.sub
        (isHomogeneous_comp_of_eq d.isHomogeneous_leftHomotopy d.isHomogeneous_inv)
        (isHomogeneous_comp_of_eq d.isHomogeneous_inv d.isHomogeneous_rightHomotopy)

/-- The rectified right chain homotopy still satisfies `f₁ g₁ - id_B = d_B k_B' + k_B' d_B`. -/
theorem linearPart_comp_inv_sub_id_rectified :
    f.linearPart ∘ₗ d.inv - LinearMap.id =
      BB.differential ∘ₗ d.rectifiedRightHomotopy + d.rectifiedRightHomotopy ∘ₗ BB.differential :=
  LinearMap.ext fun b ↦ by
    have hf : ∀ a, BB.differential (f.linearPart a) = f.linearPart (AA.differential a) :=
      LinearMap.congr_fun f.differential_comp_linearPart
    simp only [rectifiedRightHomotopy, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.id_apply, map_add, map_sub, hf, d.differential_inv_apply,
      d.differential_leftHomotopy_apply, d.differential_rightHomotopy_apply]
    abel

private theorem differential_rectifiedRightHomotopy_apply (b : B) :
    BB.differential (d.rectifiedRightHomotopy b) =
      f.linearPart (d.inv b) - b - d.rectifiedRightHomotopy (BB.differential b) :=
  eq_sub_of_add_eq (LinearMap.congr_fun d.linearPart_comp_inv_sub_id_rectified b).symm

/-- Vogt's 2-homotopy `f₁ k_A² - k_B f₁ k_A + k_B² f₁` of degree `-2` witnessing the adjointness
relation `d_B m - m d_A = f₁ k_A - k_B' f₁`. -/
private noncomputable def vogtHomotopy : A →ₗ[R] B :=
  f.linearPart ∘ₗ d.leftHomotopy ∘ₗ d.leftHomotopy -
    d.rightHomotopy ∘ₗ f.linearPart ∘ₗ d.leftHomotopy +
    d.rightHomotopy ∘ₗ d.rightHomotopy ∘ₗ f.linearPart

private theorem isHomogeneous_vogtHomotopy :
    LinearMap.IsHomogeneous d.vogtHomotopy AA.grading.piece BB.grading.piece (-2) :=
  ((isHomogeneous_comp_of_eq f.isHomogeneous_linearPart
      (isHomogeneous_comp_of_eq d.isHomogeneous_leftHomotopy d.isHomogeneous_leftHomotopy)).sub
    (isHomogeneous_comp_of_eq d.isHomogeneous_rightHomotopy
      (isHomogeneous_comp_of_eq f.isHomogeneous_linearPart d.isHomogeneous_leftHomotopy))).add
    (isHomogeneous_comp_of_eq d.isHomogeneous_rightHomotopy
      (isHomogeneous_comp_of_eq d.isHomogeneous_rightHomotopy f.isHomogeneous_linearPart))

private theorem differential_comp_vogtHomotopy_sub :
    BB.differential ∘ₗ d.vogtHomotopy - d.vogtHomotopy ∘ₗ AA.differential =
      f.linearPart ∘ₗ d.leftHomotopy - d.rectifiedRightHomotopy ∘ₗ f.linearPart :=
  LinearMap.ext fun a ↦ by
    have hf : ∀ x, BB.differential (f.linearPart x) = f.linearPart (AA.differential x) :=
      LinearMap.congr_fun f.differential_comp_linearPart
    simp only [vogtHomotopy, rectifiedRightHomotopy, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.comp_apply, map_add, map_sub, hf, d.differential_leftHomotopy_apply,
      d.differential_rightHomotopy_apply]
    abel

private theorem differential_vogtHomotopy_apply (a : A) :
    BB.differential (d.vogtHomotopy a) =
      (f.linearPart (d.leftHomotopy a) - d.rectifiedRightHomotopy (f.linearPart a)) +
        d.vogtHomotopy (AA.differential a) :=
  eq_add_of_sub_eq (LinearMap.congr_fun d.differential_comp_vogtHomotopy_sub a)

end VogtRectification

/-! ### Stage 1: lifting the right homotopy inverse `(g, h_R)` -/

section Stage1

variable {f : AInfinityHom AA BB}

/-- Partial Taylor data at filtration level `n` for lifting `d.inv` to `g : B ⟶ A` and
`d.rectifiedRightHomotopy` to `h_R : Homotopy (f.comp g) (id BB)`. -/
private structure Stage1Approx (d : f.LinearHomotopyInverse) (n : ℕ) where
  γ : ReducedTensorWords R B →ₗ[R] A
  hγ : LinearMap.IsHomogeneous γ (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0
  η : ReducedTensorWords R B →ₗ[R] B
  hη : LinearMap.IsHomogeneous η (gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece (-1)
  vanishG : ∀ z ∈ filtration R B n,
    AA.barDifferential (coalgHom R γ z) = coalgHom R γ (BB.barDifferential z)
  vanishH : ∀ z ∈ filtration R B n,
    f.barMap (coalgHom R γ z) - z =
      BB.barDifferential
        (gradedCoderivAlong (BB.grading.shift 1) 1 (f.barMap ∘ₗ coalgHom R γ) LinearMap.id η z) +
      gradedCoderivAlong (BB.grading.shift 1) 1 (f.barMap ∘ₗ coalgHom R γ) LinearMap.id η
        (BB.barDifferential z)

private noncomputable def Stage1Approx.barG {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R A :=
  coalgHom R s.γ

private noncomputable def Stage1Approx.barH {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B :=
  gradedCoderivAlong (BB.grading.shift 1) 1 (f.barMap ∘ₗ s.barG) LinearMap.id s.η

private noncomputable def Stage1Approx.errG {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R A :=
  AA.barDifferential ∘ₗ s.barG - s.barG ∘ₗ BB.barDifferential

private noncomputable def Stage1Approx.errH {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B :=
  (f.barMap ∘ₗ s.barG - LinearMap.id) -
    (BB.barDifferential ∘ₗ s.barH + s.barH ∘ₗ BB.barDifferential)

private theorem Stage1Approx.errG_eq_zero {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) {w : ReducedTensorWords R B} (hw : w ∈ filtration R B n) :
    s.errG w = 0 := by
  rw [Stage1Approx.errG, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    Stage1Approx.barG, s.vanishG w hw, sub_self]

private theorem Stage1Approx.errH_eq_zero {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) {w : ReducedTensorWords R B} (hw : w ∈ filtration R B n) :
    s.errH w = 0 := by
  rw [Stage1Approx.errH, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.id_apply,
    Stage1Approx.barH, Stage1Approx.barG, s.vanishH w hw, sub_self]

private theorem Stage1Approx.isHomogeneous_barG {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) :
    LinearMap.IsHomogeneous s.barG (gradedPiece (BB.grading.shift 1))
      (gradedPiece (AA.grading.shift 1)) 0 := by
  rw [Stage1Approx.barG]
  exact isHomogeneous_coalgHom s.hγ

private theorem Stage1Approx.isHomogeneous_barH {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) :
    LinearMap.IsHomogeneous s.barH (gradedPiece (BB.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) (-1) := by
  rw [Stage1Approx.barH]
  exact isHomogeneous_gradedCoderivAlong
    (isHomogeneous_comp_of_eq f.isHomogeneous_barMap s.isHomogeneous_barG)
    (LinearMap.isHomogeneous_id _) s.hη

private theorem Stage1Approx.isGradedCoderivationAlong_errG {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) :
    IsGradedCoderivationAlong (BB.grading.shift 1) 1 s.barG s.barG s.errG := by
  have hG : IsCoalgHom R s.barG := by rw [Stage1Approx.barG]; exact isCoalgHom_coalgHom s.γ
  rw [Stage1Approx.errG]
  exact (AA.isGradedCoderivation_barDifferential.comp_isCoalgHom hG s.isHomogeneous_barG).sub
    (hG.comp_isGradedCoderivation BB.isGradedCoderivation_barDifferential)

private theorem Stage1Approx.errG_eq_ofLetter {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) {z : ReducedTensorWords R B} (hz : z ∈ filtration R B (n + 1)) :
    s.errG z = ofLetter R A (letter R A (s.errG z)) :=
  s.isGradedCoderivationAlong_errG.eq_ofLetter_of_mem_filtration_succ
    (fun _ hw ↦ by rw [s.errG_eq_zero hw, map_zero]) hz

private theorem Stage1Approx.errH_eq_ofLetter {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) {z : ReducedTensorWords R B} (hz : z ∈ filtration R B (n + 1)) :
    s.errH z = ofLetter R B (letter R B (s.errH z)) := by
  have hG : IsCoalgHom R s.barG := by rw [Stage1Approx.barG]; exact isCoalgHom_coalgHom s.γ
  have hFG : ∀ w ∈ filtration R B n,
      BB.barDifferential ((f.barMap ∘ₗ s.barG) w) = (f.barMap ∘ₗ s.barG) (BB.barDifferential w) :=
    fun w hw ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, f.barDifferential_barMap,
        Stage1Approx.barG, s.vanishG w hw]
  have hΔ₁ := LinearMap.congr_fun (isGradedCoderivationAlong_iff.1
    ((f.isCoalgHom_barMap.comp hG).isGradedCoderivationAlong_sub (G := BB.grading.shift 1)
      (isCoalgHom_id (R := R) (M := B)))) z
  rw [InternalGrading.koszulTwist_zero, ReducedTensorWords.map_id, LinearMap.rTensor_id,
    LinearMap.id_comp] at hΔ₁
  have hH_cod : IsGradedCoderivationAlong (BB.grading.shift 1) 1 (f.barMap ∘ₗ s.barG) LinearMap.id
      s.barH := by
    rw [Stage1Approx.barH]
    exact isGradedCoderivationAlong_gradedCoderivAlong (BB.grading.shift 1) 1
      (f.isCoalgHom_barMap.comp hG) (isCoalgHom_id (R := R) (M := B)) s.η
  have hΔ₂ := hH_cod.deconcatenation_comp_add_comp_of_mem_filtration s.isHomogeneous_barH
    (by decide) BB.isGradedCoderivation_barDifferential BB.isHomogeneous_barDifferential
    (by decide) BB.isGradedCoderivation_barDifferential
    (isHomogeneous_comp_of_eq f.isHomogeneous_barMap s.isHomogeneous_barG)
    hFG (fun _ _ ↦ rfl) hz
  refine eq_ofLetter_of_deconcatenation_eq_of_mem_filtration
    (F := f.barMap ∘ₗ s.barG) (F' := LinearMap.id) (fun _ hw ↦ s.errH_eq_zero hw) hz ?_
  let U := f.barMap ∘ₗ s.barG - LinearMap.id
  let V := BB.barDifferential ∘ₗ s.barH + s.barH ∘ₗ BB.barDifferential
  have hErr : s.errH = U + (-1 : R) • V := LinearMap.ext fun w ↦ by
    simp only [U, V, Stage1Approx.errH, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, neg_one_smul]
    abel
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at hΔ₁
  rw [hErr, LinearMap.add_apply U ((-1 : R) • V) z, LinearMap.smul_apply, map_add, map_smul,
    hΔ₁, hΔ₂, smul_add, TensorProduct.map_add_left U ((-1 : R) • V), TensorProduct.map_smul_left,
    TensorProduct.map_add_right (f.barMap ∘ₗ s.barG) U ((-1 : R) • V), TensorProduct.map_smul_right,
    LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    add_add_add_comm]

/-- Arity-one base case of Stage 1 (`n = 1`). -/
private noncomputable def stage1Base (d : f.LinearHomotopyInverse) : Stage1Approx d 1 where
  γ := d.inv ∘ₗ letter R B
  hγ := isHomogeneous_comp_of_eq
    (LinearMap.isHomogeneous_shift_piece_iff.2 d.isHomogeneous_inv)
    (isHomogeneous_letter (BB.grading.shift 1))
  η := d.rectifiedRightHomotopy ∘ₗ letter R B
  hη := isHomogeneous_comp_of_eq
    (LinearMap.isHomogeneous_shift_piece_iff.2 d.isHomogeneous_rectifiedRightHomotopy)
    (isHomogeneous_letter (BB.grading.shift 1))
  vanishG _ hz :=
    eq_of_mem_filtration_one
      (AA.barDifferential ∘ₗ coalgHom R (d.inv ∘ₗ letter R B))
      (coalgHom R (d.inv ∘ₗ letter R B) ∘ₗ BB.barDifferential)
      (fun b ↦ by
        simp only [LinearMap.comp_apply, coalgHom_ofLetter, letter_ofLetter,
          AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply,
          d.differential_inv_apply]) hz
  vanishH _ hz :=
    let H₀ := gradedCoderivAlong (BB.grading.shift 1) 1
      (f.barMap ∘ₗ coalgHom R (d.inv ∘ₗ letter R B)) LinearMap.id
      (d.rectifiedRightHomotopy ∘ₗ letter R B)
    eq_of_mem_filtration_one
      (f.barMap ∘ₗ coalgHom R (d.inv ∘ₗ letter R B) - LinearMap.id)
      (BB.barDifferential ∘ₗ H₀ + H₀ ∘ₗ BB.barDifferential)
      (fun b ↦ by
        have hb := LinearMap.congr_fun d.linearPart_comp_inv_sub_id_rectified b
        simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
          LinearMap.id_apply] at hb
        simp only [H₀, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
          LinearMap.id_apply, coalgHom_ofLetter, gradedCoderivAlong_ofLetter, letter_ofLetter,
          barMap_ofLetter, AInfinityAlgebra.barDifferential_ofLetter,
          ← AInfinityAlgebra.differential_apply, ← map_sub, ← map_add, hb]) hz

private noncomputable def Stage1Approx.obsG {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) : ReducedTensorWords R B →ₗ[R] A :=
  (letter R A ∘ₗ s.errG) ∘ₗ lengthProj R B ⟨n + 1, n.succ_pos⟩

private noncomputable def Stage1Approx.obsH {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) : ReducedTensorWords R B →ₗ[R] B :=
  (letter R B ∘ₗ s.errH) ∘ₗ lengthProj R B ⟨n + 1, n.succ_pos⟩

private theorem Stage1Approx.isHomogeneous_obsG {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) :
    LinearMap.IsHomogeneous s.obsG (gradedPiece (BB.grading.shift 1))
      (AA.grading.shift 1).piece 1 := by
  have herr : LinearMap.IsHomogeneous s.errG (gradedPiece (BB.grading.shift 1))
      (gradedPiece (AA.grading.shift 1)) 1 := by
    rw [Stage1Approx.errG]
    exact (isHomogeneous_comp_of_eq AA.isHomogeneous_barDifferential s.isHomogeneous_barG).sub
      (isHomogeneous_comp_of_eq s.isHomogeneous_barG BB.isHomogeneous_barDifferential)
  rw [Stage1Approx.obsG]
  exact isHomogeneous_comp_of_eq
    (isHomogeneous_comp_of_eq (isHomogeneous_letter (AA.grading.shift 1)) herr)
    (isHomogeneous_lengthProj (BB.grading.shift 1) _)

private theorem Stage1Approx.isHomogeneous_obsH {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) :
    LinearMap.IsHomogeneous s.obsH (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece 0 := by
  have herr : LinearMap.IsHomogeneous s.errH (gradedPiece (BB.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) 0 := by
    rw [Stage1Approx.errH]
    exact ((isHomogeneous_comp_of_eq f.isHomogeneous_barMap s.isHomogeneous_barG).sub
        (LinearMap.isHomogeneous_id _)).sub
      ((isHomogeneous_comp_of_eq BB.isHomogeneous_barDifferential s.isHomogeneous_barH).add
        (isHomogeneous_comp_of_eq s.isHomogeneous_barH BB.isHomogeneous_barDifferential))
  rw [Stage1Approx.obsH]
  exact isHomogeneous_comp_of_eq
    (isHomogeneous_comp_of_eq (isHomogeneous_letter (BB.grading.shift 1)) herr)
    (isHomogeneous_lengthProj (BB.grading.shift 1) _)

/-- Bianchi identity `Φ ∘ b_B^{unary} = -d_A ∘ Φ` for the Stage 1 morphism obstruction. -/
private theorem Stage1Approx.obsG_comp_unaryBarDifferential {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) :
    s.obsG ∘ₗ BB.unaryBarDifferential = -(AA.differential ∘ₗ s.obsG) := by
  refine LinearMap.ext fun z ↦ ?_
  set w := lengthProj R B ⟨n + 1, n.succ_pos⟩ z
  have hw : w ∈ filtration R B (n + 1) := lengthProj_mem_filtration R B ⟨n + 1, n.succ_pos⟩ z
  have hbianchi : AA.barDifferential (s.errG w) + s.errG (BB.barDifferential w) = 0 := by
    simp only [Stage1Approx.errG, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
    have hA := LinearMap.congr_fun AA.barDifferential_sq (s.barG w)
    have hB := LinearMap.congr_fun BB.barDifferential_sq w
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hA hB
    rw [hA, hB, map_zero]
    abel
  have hl₂ : letter R A (s.errG (BB.barDifferential w)) =
      letter R A (s.errG (BB.unaryBarDifferential w)) :=
    apply_barDifferential_eq_unary_of_mem_filtration BB (letter R A ∘ₗ s.errG)
      (fun _ hu ↦ by rw [LinearMap.comp_apply, s.errG_eq_zero hu, map_zero]) hw
  have hl := congrArg (letter R A) hbianchi
  rw [map_add, map_zero, s.errG_eq_ofLetter hw, AInfinityAlgebra.barDifferential_ofLetter,
    letter_ofLetter, ← AInfinityAlgebra.differential_apply, hl₂] at hl
  have hcomm := LinearMap.congr_fun (lengthProj_comp_unaryBarDifferential BB ⟨n + 1, n.succ_pos⟩) z
  simp only [Stage1Approx.obsG, LinearMap.comp_apply, LinearMap.neg_apply] at hcomm ⊢
  rw [hcomm]
  exact eq_neg_of_add_eq_zero_right hl

/-- Coupled cocycle identity `Ψ ∘ b_B^{unary} = d_B ∘ Ψ - f₁ ∘ Φ` for the Stage 1 homotopy
obstruction. -/
private theorem Stage1Approx.obsH_comp_unaryBarDifferential {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) :
    s.obsH ∘ₗ BB.unaryBarDifferential = BB.differential ∘ₗ s.obsH - f.linearPart ∘ₗ s.obsG := by
  refine LinearMap.ext fun z ↦ ?_
  set w := lengthProj R B ⟨n + 1, n.succ_pos⟩ z
  have hw : w ∈ filtration R B (n + 1) := lengthProj_mem_filtration R B ⟨n + 1, n.succ_pos⟩ z
  have hrel : BB.barDifferential (s.errH w) - s.errH (BB.barDifferential w) =
      f.barMap (s.errG w) := by
    simp only [Stage1Approx.errH, Stage1Approx.errG, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.id_apply, map_sub, map_add, f.barDifferential_barMap]
    have hB₁ := LinearMap.congr_fun BB.barDifferential_sq (s.barH w)
    have hB₂ := LinearMap.congr_fun BB.barDifferential_sq w
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hB₁ hB₂
    rw [hB₁, hB₂, map_zero]
    abel
  have hl₂ : letter R B (s.errH (BB.barDifferential w)) =
      letter R B (s.errH (BB.unaryBarDifferential w)) :=
    apply_barDifferential_eq_unary_of_mem_filtration BB (letter R B ∘ₗ s.errH)
      (fun _ hu ↦ by rw [LinearMap.comp_apply, s.errH_eq_zero hu, map_zero]) hw
  have hl := congrArg (letter R B) hrel
  rw [map_sub, s.errH_eq_ofLetter hw, s.errG_eq_ofLetter hw,
    AInfinityAlgebra.barDifferential_ofLetter, barMap_ofLetter, letter_ofLetter, letter_ofLetter,
    ← AInfinityAlgebra.differential_apply, hl₂] at hl
  have hcomm := LinearMap.congr_fun (lengthProj_comp_unaryBarDifferential BB ⟨n + 1, n.succ_pos⟩) z
  simp only [Stage1Approx.obsH, Stage1Approx.obsG, LinearMap.comp_apply,
    LinearMap.sub_apply] at hcomm ⊢
  rw [hcomm, ← hl, sub_sub_cancel]

private noncomputable def Stage1Approx.corrG {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) : ReducedTensorWords R B →ₗ[R] A :=
  -(d.inv ∘ₗ s.obsH) + d.leftHomotopy ∘ₗ s.obsG

private noncomputable def Stage1Approx.corrH {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) : ReducedTensorWords R B →ₗ[R] B :=
  -(d.rectifiedRightHomotopy ∘ₗ s.obsH) + d.vogtHomotopy ∘ₗ s.obsG

private theorem Stage1Approx.corrG_eq_zero_of_mem_filtration {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) {w : ReducedTensorWords R B} (hw : w ∈ filtration R B n) :
    s.corrG w = 0 := by
  simp only [Stage1Approx.corrG, Stage1Approx.obsG, Stage1Approx.obsH, LinearMap.add_apply,
    LinearMap.neg_apply, LinearMap.comp_apply,
    lengthProj_apply_eq_zero_of_mem_filtration R B (n := ⟨n + 1, n.succ_pos⟩)
      (Nat.lt_succ_self n) hw, map_zero, neg_zero, add_zero]

private theorem Stage1Approx.corrH_eq_zero_of_mem_filtration {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) {w : ReducedTensorWords R B} (hw : w ∈ filtration R B n) :
    s.corrH w = 0 := by
  simp only [Stage1Approx.corrH, Stage1Approx.obsG, Stage1Approx.obsH, LinearMap.add_apply,
    LinearMap.neg_apply, LinearMap.comp_apply,
    lengthProj_apply_eq_zero_of_mem_filtration R B (n := ⟨n + 1, n.succ_pos⟩)
      (Nat.lt_succ_self n) hw, map_zero, neg_zero, add_zero]

private theorem Stage1Approx.kill_obsG {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) (z : ReducedTensorWords R B) :
    AA.differential (s.corrG z) - s.corrG (BB.unaryBarDifferential z) = -s.obsG z := by
  have hG := LinearMap.congr_fun s.obsG_comp_unaryBarDifferential z
  have hH := LinearMap.congr_fun s.obsH_comp_unaryBarDifferential z
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.sub_apply] at hG hH
  simp only [Stage1Approx.corrG, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply,
    map_add, map_neg, hG, hH, map_sub, d.differential_inv_apply,
    d.differential_leftHomotopy_apply]
  abel

private theorem Stage1Approx.kill_obsH {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) (z : ReducedTensorWords R B) :
    f.linearPart (s.corrG z) - BB.differential (s.corrH z) -
      s.corrH (BB.unaryBarDifferential z) = -s.obsH z := by
  have hG := LinearMap.congr_fun s.obsG_comp_unaryBarDifferential z
  have hH := LinearMap.congr_fun s.obsH_comp_unaryBarDifferential z
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.sub_apply] at hG hH
  simp only [Stage1Approx.corrG, Stage1Approx.corrH, LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.comp_apply, map_add, map_neg, hG, hH, map_sub,
    d.differential_rectifiedRightHomotopy_apply, d.differential_vogtHomotopy_apply]
  abel

private theorem Stage1Approx.barG_add_barDifferential {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) {z : ReducedTensorWords R B} (hz : z ∈ filtration R B (n + 1)) :
    coalgHom R (s.γ + s.corrG) (BB.barDifferential z) =
      s.barG (BB.barDifferential z) + ofLetter R A (s.corrG (BB.unaryBarDifferential z)) := by
  rw [Stage1Approx.barG, BB.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add,
    map_add, coalgHom_add_apply_of_mem_filtration_succ
      (fun _ hw ↦ s.corrG_eq_zero_of_mem_filtration hw)
      (BB.unaryBarDifferential_filtration (n + 1) ⟨z, hz, rfl⟩),
    coalgHom_apply_eq_of_mem_filtration (g := s.γ) (fun _ hw ↦ by
      rw [LinearMap.add_apply, s.corrG_eq_zero_of_mem_filtration hw, add_zero])
      (BB.higherBarDifferential_filtration n ⟨z, hz, rfl⟩)]
  abel

private theorem Stage1Approx.barH_add_barDifferential {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) {z : ReducedTensorWords R B} (hz : z ∈ filtration R B (n + 1)) :
    gradedCoderivAlong (BB.grading.shift 1) 1
        (f.barMap ∘ₗ coalgHom R (s.γ + s.corrG)) LinearMap.id (s.η + s.corrH)
        (BB.barDifferential z) =
      s.barH (BB.barDifferential z) + ofLetter R B (s.corrH (BB.unaryBarDifferential z)) := by
  have hG_eq : ∀ w ∈ filtration R B n,
      (f.barMap ∘ₗ coalgHom R (s.γ + s.corrG)) w = (f.barMap ∘ₗ coalgHom R s.γ) w := fun w hw ↦
    congrArg f.barMap <| coalgHom_apply_eq_of_mem_filtration (g := s.γ)
      (fun _ hu ↦ by rw [LinearMap.add_apply, s.corrG_eq_zero_of_mem_filtration hu, add_zero]) hw
  have hId := isCoalgHom_id (R := R) (M := B)
  rw [Stage1Approx.barH, Stage1Approx.barG, BB.barDifferential_eq_unary_add_higher,
    LinearMap.add_apply, map_add, map_add,
    gradedCoderivAlong_add_apply_of_mem_filtration_succ (G := BB.grading.shift 1)
      (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom _)) hId
      (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom _)) hId
      hG_eq (fun _ _ ↦ rfl) (fun _ hw ↦ s.corrH_eq_zero_of_mem_filtration hw)
      (BB.unaryBarDifferential_filtration (n + 1) ⟨z, hz, rfl⟩),
    gradedCoderivAlong_apply_eq_of_mem_filtration (G := BB.grading.shift 1) (φ₂ := s.η)
      (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom _)) hId
      (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom _)) hId
      hG_eq (fun _ _ ↦ rfl) (fun _ hw ↦ by
        rw [LinearMap.add_apply, s.corrH_eq_zero_of_mem_filtration hw, add_zero])
      (BB.higherBarDifferential_filtration n ⟨z, hz, rfl⟩)]
  abel

/-- Inductive step of Stage 1 (`n → n + 1`). -/
private noncomputable def stage1Step {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage1Approx d n) : Stage1Approx d (n + 1) where
  γ := s.γ + s.corrG
  hγ := s.hγ.add <| by
    rw [Stage1Approx.corrG]
    exact LinearMap.IsHomogeneous.add
      (LinearMap.IsHomogeneous.neg <|
        isHomogeneous_comp_of_eq (LinearMap.isHomogeneous_shift_piece_iff.2 d.isHomogeneous_inv)
          s.isHomogeneous_obsH)
      (isHomogeneous_comp_of_eq
        (LinearMap.isHomogeneous_shift_piece_iff.2 d.isHomogeneous_leftHomotopy)
        s.isHomogeneous_obsG)
  η := s.η + s.corrH
  hη := s.hη.add <| by
    rw [Stage1Approx.corrH]
    exact LinearMap.IsHomogeneous.add
      (LinearMap.IsHomogeneous.neg <|
        isHomogeneous_comp_of_eq
          (LinearMap.isHomogeneous_shift_piece_iff.2 d.isHomogeneous_rectifiedRightHomotopy)
          s.isHomogeneous_obsH)
      (isHomogeneous_comp_of_eq
        (LinearMap.isHomogeneous_shift_piece_iff.2 d.isHomogeneous_vogtHomotopy)
        s.isHomogeneous_obsG)
  vanishG z hz := by
    have hGz := coalgHom_add_apply_of_mem_filtration_succ (f := s.γ)
      (fun _ hw ↦ s.corrG_eq_zero_of_mem_filtration hw) hz
    have hobs : s.errG z = ofLetter R A (s.obsG z) := by
      rw [s.errG_eq_ofLetter hz, Stage1Approx.obsG, LinearMap.comp_apply,
        apply_lengthProj_of_mem_filtration R B
          (fun _ hw ↦ by rw [LinearMap.comp_apply, s.errG_eq_zero hw, map_zero]) hz,
        LinearMap.comp_apply]
    have hkill := eq_add_of_sub_eq (s.kill_obsG z)
    rw [hGz, s.barG_add_barDifferential hz, map_add, AInfinityAlgebra.barDifferential_ofLetter,
      ← AInfinityAlgebra.differential_apply, hkill, map_add, map_neg, ← hobs]
    simp only [Stage1Approx.errG, Stage1Approx.barG, LinearMap.sub_apply, LinearMap.comp_apply]
    abel
  vanishH z hz := by
    have hG_eq : ∀ w ∈ filtration R B n,
        (f.barMap ∘ₗ coalgHom R (s.γ + s.corrG)) w = (f.barMap ∘ₗ coalgHom R s.γ) w := fun w hw ↦
      congrArg f.barMap <| coalgHom_apply_eq_of_mem_filtration (g := s.γ)
        (fun _ hu ↦ by rw [LinearMap.add_apply, s.corrG_eq_zero_of_mem_filtration hu, add_zero]) hw
    have hId := isCoalgHom_id (R := R) (M := B)
    have hGz := coalgHom_add_apply_of_mem_filtration_succ (f := s.γ)
      (fun _ hw ↦ s.corrG_eq_zero_of_mem_filtration hw) hz
    have hHz := gradedCoderivAlong_add_apply_of_mem_filtration_succ (G := BB.grading.shift 1)
      (q := 1) (φ := s.η) (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom _)) hId
      (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom _)) hId
      hG_eq (fun _ _ ↦ rfl) (fun _ hw ↦ s.corrH_eq_zero_of_mem_filtration hw) hz
    have hobs : s.errH z = ofLetter R B (s.obsH z) := by
      rw [s.errH_eq_ofLetter hz, Stage1Approx.obsH, LinearMap.comp_apply,
        apply_lengthProj_of_mem_filtration R B
          (fun _ hw ↦ by rw [LinearMap.comp_apply, s.errH_eq_zero hw, map_zero]) hz,
        LinearMap.comp_apply]
    have hkill := eq_add_of_sub_eq (eq_add_of_sub_eq (s.kill_obsH z))
    rw [hGz, hHz, s.barH_add_barDifferential hz, map_add, map_add, barMap_ofLetter,
      AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply, hkill,
      map_add, map_add, map_neg, ← hobs]
    simp only [Stage1Approx.errH, Stage1Approx.barH, Stage1Approx.barG, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply]
    abel

private noncomputable def stage1Seq (d : f.LinearHomotopyInverse) :
    ∀ m : ℕ, Stage1Approx d (m + 1)
  | 0 => stage1Base d
  | m + 1 => stage1Step (stage1Seq d m)

private theorem stage1Seq_γ_stabilises (d : f.LinearHomotopyInverse) (m : ℕ)
    (z : ReducedTensorWords R B) (hz : z ∈ filtration R B (m + 1)) :
    (stage1Seq d (m + 1)).γ z = (stage1Seq d m).γ z := by
  rw [stage1Seq, stage1Step, LinearMap.add_apply,
    (stage1Seq d m).corrG_eq_zero_of_mem_filtration hz, add_zero]

private theorem stage1Seq_η_stabilises (d : f.LinearHomotopyInverse) (m : ℕ)
    (z : ReducedTensorWords R B) (hz : z ∈ filtration R B (m + 1)) :
    (stage1Seq d (m + 1)).η z = (stage1Seq d m).η z := by
  rw [stage1Seq, stage1Step, LinearMap.add_apply,
    (stage1Seq d m).corrH_eq_zero_of_mem_filtration hz, add_zero]

/-- The **`A∞` homotopy inverse** `g : B ⟶ A` lifted from a chain-homotopy inverse `d` of
`f.linearPart`. -/
noncomputable def homotopyInverse (d : f.LinearHomotopyInverse) : AInfinityHom BB AA :=
  ofTaylor (stabilisingTaylor fun m ↦ (stage1Seq d m).γ)
    (isHomogeneous_stabilisingTaylor (stage1Seq_γ_stabilises d) fun m ↦ (stage1Seq d m).hγ)
    (LinearMap.ext fun z ↦ by
      obtain ⟨m, hm⟩ := exists_mem_filtration R B z
      have hz : z ∈ filtration R B (m + 1) := filtration_monotone R B m.le_succ hm
      have hG : coalgHom R (stabilisingTaylor fun k ↦ (stage1Seq d k).γ) z =
          coalgHom R (stage1Seq d m).γ z :=
        coalgHom_apply_eq_of_mem_filtration (g := (stage1Seq d m).γ)
          (fun _ hw ↦ stabilisingTaylor_apply_of_mem_filtration (stage1Seq_γ_stabilises d) hw) hz
      have hv := congrArg (letter R A) ((stage1Seq d m).vanishG z hz)
      have hl₁ := LinearMap.congr_fun AA.letter_comp_barDifferential
        (coalgHom R (stage1Seq d m).γ z)
      have hl₂ := LinearMap.congr_fun (letter_comp_coalgHom (stage1Seq d m).γ)
        (BB.barDifferential z)
      rw [LinearMap.comp_apply] at hl₁ hl₂
      rw [hl₁, hl₂] at hv
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hG, hv,
        stabilisingTaylor_apply_of_mem_filtration (stage1Seq_γ_stabilises d)
          (BB.barDifferential_mem_filtration hz)])

/-- The linear part of the lifted `A∞` homotopy inverse is `d.inv`. -/
@[simp]
theorem linearPart_homotopyInverse (d : f.LinearHomotopyInverse) :
    d.homotopyInverse.linearPart = d.inv :=
  LinearMap.ext fun b ↦ by
    rw [linearPart_apply, homotopyInverse, taylor_ofTaylor,
      stabilisingTaylor_apply_of_mem_filtration (stage1Seq_γ_stabilises d)
        (ofLetter_mem_filtration R B b), stage1Seq, stage1Base, LinearMap.comp_apply,
      letter_ofLetter]

/-- The lifted **right `A∞` homotopy** from `f.comp d.homotopyInverse` to `id BB`. -/
noncomputable def rightHomotopyLift (d : f.LinearHomotopyInverse) :
    Homotopy (f.comp d.homotopyInverse) (AInfinityHom.id BB) :=
  Homotopy.ofTaylor (stabilisingTaylor fun m ↦ (stage1Seq d m).η)
    (isHomogeneous_stabilisingTaylor (stage1Seq_η_stabilises d) fun m ↦ (stage1Seq d m).hη)
    (LinearMap.ext fun z ↦ by
      obtain ⟨m, hm⟩ := exists_mem_filtration R B z
      have hz : z ∈ filtration R B (m + 1) := filtration_monotone R B m.le_succ hm
      have hG : ∀ w ∈ filtration R B (m + 1),
          (f.comp d.homotopyInverse).barMap w = (f.barMap ∘ₗ coalgHom R (stage1Seq d m).γ) w :=
        fun w hw ↦ by
          rw [barMap_comp, LinearMap.comp_apply, LinearMap.comp_apply, homotopyInverse,
            barMap_ofTaylor, coalgHom_apply_eq_of_mem_filtration (g := (stage1Seq d m).γ)
              (fun _ hu ↦ stabilisingTaylor_apply_of_mem_filtration (stage1Seq_γ_stabilises d) hu)
              hw]
      have hH : gradedCoderivAlong (BB.grading.shift 1) 1 (f.comp d.homotopyInverse).barMap
          LinearMap.id (stabilisingTaylor fun k ↦ (stage1Seq d k).η) z =
          (stage1Seq d m).barH z := by
        rw [Stage1Approx.barH, Stage1Approx.barG]
        exact gradedCoderivAlong_apply_eq_of_mem_filtration (G := BB.grading.shift 1)
          (φ₂ := (stage1Seq d m).η)
          (f.comp d.homotopyInverse).isCoalgHom_barMap (isCoalgHom_id (R := R) (M := B))
          (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom _)) (isCoalgHom_id (R := R) (M := B))
          hG (fun _ _ ↦ rfl)
          (fun _ hw ↦ stabilisingTaylor_apply_of_mem_filtration (stage1Seq_η_stabilises d) hw) hz
      have hv := congrArg (letter R B) ((stage1Seq d m).vanishH z hz)
      have hl₁ := LinearMap.congr_fun BB.letter_comp_barDifferential ((stage1Seq d m).barH z)
      have hl₂ := LinearMap.congr_fun (letter_comp_gradedCoderivAlong (BB.grading.shift 1) 1
        (f.barMap ∘ₗ coalgHom R (stage1Seq d m).γ) LinearMap.id (stage1Seq d m).η)
        (BB.barDifferential z)
      rw [LinearMap.comp_apply, Stage1Approx.barH, Stage1Approx.barG] at hl₁
      rw [LinearMap.comp_apply] at hl₂
      rw [map_sub, map_add, hl₁, hl₂] at hv
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
        AInfinityHom.taylor_def, barMap_id, LinearMap.id_apply]
      rw [hG z hz, hH, Stage1Approx.barH, Stage1Approx.barG,
        stabilisingTaylor_apply_of_mem_filtration (stage1Seq_η_stabilises d)
          (BB.barDifferential_mem_filtration hz), LinearMap.comp_apply]
      exact hv)

/-- The arity-one component of `d.rightHomotopyLift` is Vogt's rectified right homotopy. -/
@[simp]
theorem linearHomotopy_rightHomotopyLift (d : f.LinearHomotopyInverse) :
    d.rightHomotopyLift.linearHomotopy = d.rectifiedRightHomotopy :=
  LinearMap.ext fun b ↦ by
    rw [rightHomotopyLift, Homotopy.linearHomotopy_ofTaylor, LinearMap.comp_apply,
      stabilisingTaylor_apply_of_mem_filtration (stage1Seq_η_stabilises d)
        (ofLetter_mem_filtration R B b), stage1Seq, stage1Base, LinearMap.comp_apply,
      letter_ofLetter]

end Stage1

/-! ### Stage 2: lifting the left homotopy `h_L` -/

section Stage2

variable {f : AInfinityHom AA BB}

/-- Partial Taylor data at filtration level `n` for lifting `d.leftHomotopy` to
`h_L : Homotopy (d.homotopyInverse.comp f) (id AA)` together with its degree-`-2` coherence
coderivation `M`. -/
private structure Stage2Approx (d : f.LinearHomotopyInverse) (n : ℕ) where
  θ : ReducedTensorWords R A →ₗ[R] A
  hθ : LinearMap.IsHomogeneous θ (gradedPiece (AA.grading.shift 1)) (AA.grading.shift 1).piece (-1)
  μ : ReducedTensorWords R A →ₗ[R] B
  hμ : LinearMap.IsHomogeneous μ (gradedPiece (AA.grading.shift 1)) (BB.grading.shift 1).piece (-2)
  vanishL : ∀ z ∈ filtration R A n,
    d.homotopyInverse.barMap (f.barMap z) - z =
      AA.barDifferential (gradedCoderivAlong (AA.grading.shift 1) 1
        (d.homotopyInverse.barMap ∘ₗ f.barMap) LinearMap.id θ z) +
      gradedCoderivAlong (AA.grading.shift 1) 1 (d.homotopyInverse.barMap ∘ₗ f.barMap)
        LinearMap.id θ (AA.barDifferential z)
  vanishM : ∀ z ∈ filtration R A n,
    d.rightHomotopyLift.barHomotopy (f.barMap z) -
      f.barMap (gradedCoderivAlong (AA.grading.shift 1) 1
        (d.homotopyInverse.barMap ∘ₗ f.barMap) LinearMap.id θ z) =
      BB.barDifferential (gradedCoderivAlong (AA.grading.shift 1) 0
        ((f.barMap ∘ₗ d.homotopyInverse.barMap) ∘ₗ f.barMap) f.barMap μ z) -
      gradedCoderivAlong (AA.grading.shift 1) 0
        ((f.barMap ∘ₗ d.homotopyInverse.barMap) ∘ₗ f.barMap) f.barMap μ (AA.barDifferential z)

private noncomputable def Stage2Approx.barL {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R A :=
  gradedCoderivAlong (AA.grading.shift 1) 1 (d.homotopyInverse.barMap ∘ₗ f.barMap)
    LinearMap.id s.θ

private noncomputable def Stage2Approx.barM {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B :=
  gradedCoderivAlong (AA.grading.shift 1) 0
    ((f.barMap ∘ₗ d.homotopyInverse.barMap) ∘ₗ f.barMap) f.barMap s.μ

private noncomputable def Stage2Approx.errL {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R A :=
  (d.homotopyInverse.barMap ∘ₗ f.barMap - LinearMap.id) -
    (AA.barDifferential ∘ₗ s.barL + s.barL ∘ₗ AA.barDifferential)

private noncomputable def Stage2Approx.errM {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B :=
  (d.rightHomotopyLift.barHomotopy ∘ₗ f.barMap - f.barMap ∘ₗ s.barL) -
    (BB.barDifferential ∘ₗ s.barM - s.barM ∘ₗ AA.barDifferential)

private theorem Stage2Approx.errL_eq_zero {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) {w : ReducedTensorWords R A} (hw : w ∈ filtration R A n) :
    s.errL w = 0 := by
  rw [Stage2Approx.errL, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.id_apply,
    Stage2Approx.barL, s.vanishL w hw, sub_self]

private theorem Stage2Approx.errM_eq_zero {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) {w : ReducedTensorWords R A} (hw : w ∈ filtration R A n) :
    s.errM w = 0 := by
  rw [Stage2Approx.errM, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    Stage2Approx.barL, Stage2Approx.barM, s.vanishM w hw, sub_self]

private theorem Stage2Approx.isHomogeneous_barL {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) :
    LinearMap.IsHomogeneous s.barL (gradedPiece (AA.grading.shift 1))
      (gradedPiece (AA.grading.shift 1)) (-1) := by
  rw [Stage2Approx.barL]
  exact isHomogeneous_gradedCoderivAlong
    (isHomogeneous_comp_of_eq d.homotopyInverse.isHomogeneous_barMap f.isHomogeneous_barMap)
    (LinearMap.isHomogeneous_id _) s.hθ

private theorem Stage2Approx.isHomogeneous_barM {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) :
    LinearMap.IsHomogeneous s.barM (gradedPiece (AA.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) (-2) := by
  rw [Stage2Approx.barM]
  exact isHomogeneous_gradedCoderivAlong
    (isHomogeneous_comp_of_eq
      (isHomogeneous_comp_of_eq f.isHomogeneous_barMap d.homotopyInverse.isHomogeneous_barMap)
      f.isHomogeneous_barMap)
    f.isHomogeneous_barMap s.hμ

private theorem Stage2Approx.isGradedCoderivationAlong_errL {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) :
    IsGradedCoderivationAlong (AA.grading.shift 1) 0
      (d.homotopyInverse.barMap ∘ₗ f.barMap) LinearMap.id s.errL := by
  have hId := isCoalgHom_id (R := R) (M := A)
  have hGF : IsCoalgHom R (d.homotopyInverse.barMap ∘ₗ f.barMap) :=
    d.homotopyInverse.isCoalgHom_barMap.comp f.isCoalgHom_barMap
  have hGF₀ := isHomogeneous_comp_of_eq d.homotopyInverse.isHomogeneous_barMap
    f.isHomogeneous_barMap
  have hGFb : AA.barDifferential ∘ₗ (d.homotopyInverse.barMap ∘ₗ f.barMap) =
      (d.homotopyInverse.barMap ∘ₗ f.barMap) ∘ₗ AA.barDifferential := by
    rw [← LinearMap.comp_assoc, d.homotopyInverse.barDifferential_comp_barMap,
      LinearMap.comp_assoc, f.barDifferential_comp_barMap, LinearMap.comp_assoc]
  have hL_cod : IsGradedCoderivationAlong (AA.grading.shift 1) 1
      (d.homotopyInverse.barMap ∘ₗ f.barMap) LinearMap.id s.barL := by
    rw [Stage2Approx.barL]
    exact isGradedCoderivationAlong_gradedCoderivAlong (AA.grading.shift 1) 1 hGF hId s.θ
  rw [Stage2Approx.errL]
  exact (hGF.isGradedCoderivationAlong_sub hId).sub <|
    hL_cod.comp_add_comp s.isHomogeneous_barL (by decide)
      AA.isGradedCoderivation_barDifferential AA.isHomogeneous_barDifferential (by decide)
      AA.isGradedCoderivation_barDifferential hGF₀ hGFb
      (by rw [LinearMap.comp_id, LinearMap.id_comp])

private theorem Stage2Approx.isGradedCoderivationAlong_errM {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) :
    IsGradedCoderivationAlong (AA.grading.shift 1) 1
      ((f.barMap ∘ₗ d.homotopyInverse.barMap) ∘ₗ f.barMap) f.barMap s.errM := by
  have hId := isCoalgHom_id (R := R) (M := A)
  have hL_cod : IsGradedCoderivationAlong (AA.grading.shift 1) 1
      (d.homotopyInverse.barMap ∘ₗ f.barMap) LinearMap.id s.barL := by
    rw [Stage2Approx.barL]
    exact isGradedCoderivationAlong_gradedCoderivAlong (AA.grading.shift 1) 1
      (d.homotopyInverse.isCoalgHom_barMap.comp f.isCoalgHom_barMap) hId s.θ
  have h₁ : IsGradedCoderivationAlong (AA.grading.shift 1) 1
      ((f.barMap ∘ₗ d.homotopyInverse.barMap) ∘ₗ f.barMap) f.barMap
      (d.rightHomotopyLift.barHomotopy ∘ₗ f.barMap - f.barMap ∘ₗ s.barL) := by
    have ha := d.rightHomotopyLift.isGradedCoderivationAlong_barHomotopy.comp_isCoalgHom
      f.isCoalgHom_barMap f.isHomogeneous_barMap
    rw [barMap_comp, barMap_id, LinearMap.id_comp] at ha
    have hb := f.isCoalgHom_barMap.comp_isGradedCoderivationAlong hL_cod
    rw [LinearMap.comp_id, ← LinearMap.comp_assoc] at hb
    exact ha.sub hb
  have hFGF₀ := isHomogeneous_comp_of_eq
    (isHomogeneous_comp_of_eq f.isHomogeneous_barMap d.homotopyInverse.isHomogeneous_barMap)
    f.isHomogeneous_barMap
  have hFGFb : BB.barDifferential ∘ₗ ((f.barMap ∘ₗ d.homotopyInverse.barMap) ∘ₗ f.barMap) =
      ((f.barMap ∘ₗ d.homotopyInverse.barMap) ∘ₗ f.barMap) ∘ₗ AA.barDifferential := by
    rw [← barMap_comp, ← barMap_comp, barDifferential_comp_barMap]
  have hM_cod : IsGradedCoderivationAlong (AA.grading.shift 1) 0
      ((f.barMap ∘ₗ d.homotopyInverse.barMap) ∘ₗ f.barMap) f.barMap s.barM := by
    rw [Stage2Approx.barM]
    exact isGradedCoderivationAlong_gradedCoderivAlong (AA.grading.shift 1) 0
      ((f.isCoalgHom_barMap.comp d.homotopyInverse.isCoalgHom_barMap).comp f.isCoalgHom_barMap)
      f.isCoalgHom_barMap s.μ
  have h₂ := hM_cod.comp_sub_negOnePow_smul_comp s.isHomogeneous_barM
    AA.isGradedCoderivation_barDifferential AA.isHomogeneous_barDifferential (by decide)
    BB.isGradedCoderivation_barDifferential hFGF₀ hFGFb f.barDifferential_comp_barMap
  have hp : (1 * (-2) : ℤ).negOnePow = 1 := by decide
  rw [zero_add, hp, Units.val_one, Int.cast_one, one_smul] at h₂
  rw [Stage2Approx.errM]
  exact h₁.sub h₂

private theorem Stage2Approx.errL_eq_ofLetter {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) {z : ReducedTensorWords R A} (hz : z ∈ filtration R A (n + 1)) :
    s.errL z = ofLetter R A (letter R A (s.errL z)) :=
  s.isGradedCoderivationAlong_errL.eq_ofLetter_of_mem_filtration_succ
    (fun _ hw ↦ by rw [s.errL_eq_zero hw, map_zero]) hz

private theorem Stage2Approx.errM_eq_ofLetter {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) {z : ReducedTensorWords R A} (hz : z ∈ filtration R A (n + 1)) :
    s.errM z = ofLetter R B (letter R B (s.errM z)) :=
  s.isGradedCoderivationAlong_errM.eq_ofLetter_of_mem_filtration_succ
    (fun _ hw ↦ by rw [s.errM_eq_zero hw, map_zero]) hz

/-- Arity-one base case of Stage 2 (`n = 1`). -/
private noncomputable def stage2Base (d : f.LinearHomotopyInverse) : Stage2Approx d 1 where
  θ := d.leftHomotopy ∘ₗ letter R A
  hθ := isHomogeneous_comp_of_eq
    (LinearMap.isHomogeneous_shift_piece_iff.2 d.isHomogeneous_leftHomotopy)
    (isHomogeneous_letter (AA.grading.shift 1))
  μ := (-d.vogtHomotopy) ∘ₗ letter R A
  hμ := isHomogeneous_comp_of_eq
    (LinearMap.isHomogeneous_shift_piece_iff.2 d.isHomogeneous_vogtHomotopy).neg
    (isHomogeneous_letter (AA.grading.shift 1))
  vanishL _ hz :=
    let L₀ := gradedCoderivAlong (AA.grading.shift 1) 1
      (d.homotopyInverse.barMap ∘ₗ f.barMap) LinearMap.id (d.leftHomotopy ∘ₗ letter R A)
    eq_of_mem_filtration_one
      (d.homotopyInverse.barMap ∘ₗ f.barMap - LinearMap.id)
      (AA.barDifferential ∘ₗ L₀ + L₀ ∘ₗ AA.barDifferential)
      (fun a ↦ by
        have ha := LinearMap.congr_fun d.inv_comp_linearPart_sub_id a
        simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
          LinearMap.id_apply] at ha
        simp only [L₀, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
          LinearMap.id_apply, gradedCoderivAlong_ofLetter, letter_ofLetter, barMap_ofLetter,
          linearPart_homotopyInverse, AInfinityAlgebra.barDifferential_ofLetter,
          ← AInfinityAlgebra.differential_apply, ← map_sub, ← map_add, ha]) hz
  vanishM _ hz :=
    let L₀ := gradedCoderivAlong (AA.grading.shift 1) 1
      (d.homotopyInverse.barMap ∘ₗ f.barMap) LinearMap.id (d.leftHomotopy ∘ₗ letter R A)
    let M₀ := gradedCoderivAlong (AA.grading.shift 1) 0
      ((f.barMap ∘ₗ d.homotopyInverse.barMap) ∘ₗ f.barMap) f.barMap
      ((-d.vogtHomotopy) ∘ₗ letter R A)
    eq_of_mem_filtration_one
      (d.rightHomotopyLift.barHomotopy ∘ₗ f.barMap - f.barMap ∘ₗ L₀)
      (BB.barDifferential ∘ₗ M₀ - M₀ ∘ₗ AA.barDifferential)
      (fun a ↦ by
        simp only [L₀, M₀, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.neg_apply,
          gradedCoderivAlong_ofLetter, letter_ofLetter, barMap_ofLetter,
          Homotopy.barHomotopy_ofLetter, linearHomotopy_rightHomotopyLift,
          AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply,
          d.differential_vogtHomotopy_apply, map_neg, map_sub, map_add]
        abel) hz

private noncomputable def Stage2Approx.obsL {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) : ReducedTensorWords R A →ₗ[R] A :=
  (letter R A ∘ₗ s.errL) ∘ₗ lengthProj R A ⟨n + 1, n.succ_pos⟩

private noncomputable def Stage2Approx.obsM {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) : ReducedTensorWords R A →ₗ[R] B :=
  (letter R B ∘ₗ s.errM) ∘ₗ lengthProj R A ⟨n + 1, n.succ_pos⟩

private theorem Stage2Approx.isHomogeneous_obsL {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) :
    LinearMap.IsHomogeneous s.obsL (gradedPiece (AA.grading.shift 1))
      (AA.grading.shift 1).piece 0 := by
  have herr : LinearMap.IsHomogeneous s.errL (gradedPiece (AA.grading.shift 1))
      (gradedPiece (AA.grading.shift 1)) 0 := by
    rw [Stage2Approx.errL]
    exact ((isHomogeneous_comp_of_eq d.homotopyInverse.isHomogeneous_barMap f.isHomogeneous_barMap)
        |>.sub (LinearMap.isHomogeneous_id _)).sub
      ((isHomogeneous_comp_of_eq AA.isHomogeneous_barDifferential s.isHomogeneous_barL).add
        (isHomogeneous_comp_of_eq s.isHomogeneous_barL AA.isHomogeneous_barDifferential))
  rw [Stage2Approx.obsL]
  exact isHomogeneous_comp_of_eq
    (isHomogeneous_comp_of_eq (isHomogeneous_letter (AA.grading.shift 1)) herr)
    (isHomogeneous_lengthProj (AA.grading.shift 1) _)

private theorem Stage2Approx.isHomogeneous_obsM {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) :
    LinearMap.IsHomogeneous s.obsM (gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece (-1) := by
  have herr : LinearMap.IsHomogeneous s.errM (gradedPiece (AA.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) (-1) := by
    rw [Stage2Approx.errM]
    exact ((isHomogeneous_comp_of_eq d.rightHomotopyLift.isHomogeneous_barHomotopy
          f.isHomogeneous_barMap).sub
        (isHomogeneous_comp_of_eq f.isHomogeneous_barMap s.isHomogeneous_barL)).sub
      ((isHomogeneous_comp_of_eq BB.isHomogeneous_barDifferential s.isHomogeneous_barM).sub
        (isHomogeneous_comp_of_eq s.isHomogeneous_barM AA.isHomogeneous_barDifferential))
  rw [Stage2Approx.obsM]
  exact isHomogeneous_comp_of_eq
    (isHomogeneous_comp_of_eq (isHomogeneous_letter (BB.grading.shift 1)) herr)
    (isHomogeneous_lengthProj (AA.grading.shift 1) _)

/-- Cocycle identity `Θ ∘ b_A^{unary} = d_A ∘ Θ` for the Stage 2 left-homotopy obstruction. -/
private theorem Stage2Approx.obsL_comp_unaryBarDifferential {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) :
    s.obsL ∘ₗ AA.unaryBarDifferential = AA.differential ∘ₗ s.obsL := by
  refine LinearMap.ext fun z ↦ ?_
  set w := lengthProj R A ⟨n + 1, n.succ_pos⟩ z
  have hw : w ∈ filtration R A (n + 1) := lengthProj_mem_filtration R A ⟨n + 1, n.succ_pos⟩ z
  have hcocycle : AA.barDifferential (s.errL w) - s.errL (AA.barDifferential w) = 0 := by
    simp only [Stage2Approx.errL, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, map_sub, map_add, d.homotopyInverse.barDifferential_barMap,
      f.barDifferential_barMap]
    have hA₁ := LinearMap.congr_fun AA.barDifferential_sq (s.barL w)
    have hA₂ := LinearMap.congr_fun AA.barDifferential_sq w
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hA₁ hA₂
    rw [hA₁, hA₂, map_zero]
    abel
  have hl₂ : letter R A (s.errL (AA.barDifferential w)) =
      letter R A (s.errL (AA.unaryBarDifferential w)) :=
    apply_barDifferential_eq_unary_of_mem_filtration AA (letter R A ∘ₗ s.errL)
      (fun _ hu ↦ by rw [LinearMap.comp_apply, s.errL_eq_zero hu, map_zero]) hw
  have hl := congrArg (letter R A) hcocycle
  rw [map_sub, map_zero, s.errL_eq_ofLetter hw, AInfinityAlgebra.barDifferential_ofLetter,
    letter_ofLetter, ← AInfinityAlgebra.differential_apply, hl₂] at hl
  have hcomm := LinearMap.congr_fun (lengthProj_comp_unaryBarDifferential AA ⟨n + 1, n.succ_pos⟩) z
  simp only [Stage2Approx.obsL, LinearMap.comp_apply] at hcomm ⊢
  rw [hcomm]
  exact (sub_eq_zero.1 hl).symm

/-- Coupled cocycle identity `Ξ ∘ b_A^{unary} = f₁ ∘ Θ - d_B ∘ Ξ` for the Stage 2 coherence
obstruction. -/
private theorem Stage2Approx.obsM_comp_unaryBarDifferential {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) :
    s.obsM ∘ₗ AA.unaryBarDifferential = f.linearPart ∘ₗ s.obsL - BB.differential ∘ₗ s.obsM := by
  refine LinearMap.ext fun z ↦ ?_
  set w := lengthProj R A ⟨n + 1, n.succ_pos⟩ z
  have hw : w ∈ filtration R A (n + 1) := lengthProj_mem_filtration R A ⟨n + 1, n.succ_pos⟩ z
  have hrel : BB.barDifferential (s.errM w) + s.errM (AA.barDifferential w) =
      f.barMap (s.errL w) := by
    have hhR := d.rightHomotopyLift.barMap_sub_barMap_apply (f.barMap w)
    rw [barMap_comp, barMap_id, LinearMap.comp_apply, LinearMap.id_apply,
      f.barDifferential_barMap] at hhR
    have hhR' := eq_sub_of_add_eq hhR.symm
    simp only [Stage2Approx.errM, Stage2Approx.errL, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.id_apply, map_sub, map_add, f.barDifferential_barMap, hhR']
    have hB := LinearMap.congr_fun BB.barDifferential_sq (s.barM w)
    have hA := LinearMap.congr_fun AA.barDifferential_sq w
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hB hA
    rw [hB, hA, map_zero]
    abel
  have hl₂ : letter R B (s.errM (AA.barDifferential w)) =
      letter R B (s.errM (AA.unaryBarDifferential w)) :=
    apply_barDifferential_eq_unary_of_mem_filtration AA (letter R B ∘ₗ s.errM)
      (fun _ hu ↦ by rw [LinearMap.comp_apply, s.errM_eq_zero hu, map_zero]) hw
  have hl := congrArg (letter R B) hrel
  rw [map_add, s.errM_eq_ofLetter hw, s.errL_eq_ofLetter hw,
    AInfinityAlgebra.barDifferential_ofLetter, barMap_ofLetter, letter_ofLetter, letter_ofLetter,
    ← AInfinityAlgebra.differential_apply, hl₂] at hl
  have hcomm := LinearMap.congr_fun (lengthProj_comp_unaryBarDifferential AA ⟨n + 1, n.succ_pos⟩) z
  simp only [Stage2Approx.obsM, Stage2Approx.obsL, LinearMap.comp_apply,
    LinearMap.sub_apply] at hcomm ⊢
  rw [hcomm]
  exact eq_sub_of_add_eq' hl

private noncomputable def Stage2Approx.corrL {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) : ReducedTensorWords R A →ₗ[R] A :=
  d.inv ∘ₗ s.obsM - d.leftHomotopy ∘ₗ s.obsL

private noncomputable def Stage2Approx.corrM {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) : ReducedTensorWords R A →ₗ[R] B :=
  -(d.rectifiedRightHomotopy ∘ₗ s.obsM) + d.vogtHomotopy ∘ₗ s.obsL

private theorem Stage2Approx.corrL_eq_zero_of_mem_filtration {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) {w : ReducedTensorWords R A} (hw : w ∈ filtration R A n) :
    s.corrL w = 0 := by
  simp only [Stage2Approx.corrL, Stage2Approx.obsL, Stage2Approx.obsM, LinearMap.sub_apply,
    LinearMap.comp_apply,
    lengthProj_apply_eq_zero_of_mem_filtration R A (n := ⟨n + 1, n.succ_pos⟩)
      (Nat.lt_succ_self n) hw, map_zero, sub_self]

private theorem Stage2Approx.corrM_eq_zero_of_mem_filtration {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) {w : ReducedTensorWords R A} (hw : w ∈ filtration R A n) :
    s.corrM w = 0 := by
  simp only [Stage2Approx.corrM, Stage2Approx.obsL, Stage2Approx.obsM, LinearMap.add_apply,
    LinearMap.neg_apply, LinearMap.comp_apply,
    lengthProj_apply_eq_zero_of_mem_filtration R A (n := ⟨n + 1, n.succ_pos⟩)
      (Nat.lt_succ_self n) hw, map_zero, neg_zero, add_zero]

private theorem Stage2Approx.kill_obsL {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) (z : ReducedTensorWords R A) :
    AA.differential (s.corrL z) + s.corrL (AA.unaryBarDifferential z) = s.obsL z := by
  have hL := LinearMap.congr_fun s.obsL_comp_unaryBarDifferential z
  have hM := LinearMap.congr_fun s.obsM_comp_unaryBarDifferential z
  simp only [LinearMap.comp_apply, LinearMap.sub_apply] at hL hM
  simp only [Stage2Approx.corrL, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hL, hM,
    d.differential_inv_apply, d.differential_leftHomotopy_apply]
  abel

private theorem Stage2Approx.kill_obsM {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) (z : ReducedTensorWords R A) :
    f.linearPart (s.corrL z) + BB.differential (s.corrM z) -
      s.corrM (AA.unaryBarDifferential z) = s.obsM z := by
  have hL := LinearMap.congr_fun s.obsL_comp_unaryBarDifferential z
  have hM := LinearMap.congr_fun s.obsM_comp_unaryBarDifferential z
  simp only [LinearMap.comp_apply, LinearMap.sub_apply] at hL hM
  simp only [Stage2Approx.corrL, Stage2Approx.corrM, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.neg_apply, LinearMap.comp_apply, map_sub, map_add, map_neg, hL, hM,
    d.differential_rectifiedRightHomotopy_apply, d.differential_vogtHomotopy_apply]
  abel

private theorem Stage2Approx.barL_add_barDifferential {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) {z : ReducedTensorWords R A} (hz : z ∈ filtration R A (n + 1)) :
    gradedCoderivAlong (AA.grading.shift 1) 1 (d.homotopyInverse.barMap ∘ₗ f.barMap)
        LinearMap.id (s.θ + s.corrL) (AA.barDifferential z) =
      s.barL (AA.barDifferential z) + ofLetter R A (s.corrL (AA.unaryBarDifferential z)) := by
  have hId := isCoalgHom_id (R := R) (M := A)
  have hGF := d.homotopyInverse.isCoalgHom_barMap.comp f.isCoalgHom_barMap
  rw [Stage2Approx.barL, AA.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add,
    map_add, gradedCoderivAlong_add_apply_of_mem_filtration_succ (G := AA.grading.shift 1)
      hGF hId hGF hId (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun _ hw ↦ s.corrL_eq_zero_of_mem_filtration hw)
      (AA.unaryBarDifferential_filtration (n + 1) ⟨z, hz, rfl⟩),
    gradedCoderivAlong_apply_eq_of_mem_filtration (G := AA.grading.shift 1) (φ₂ := s.θ)
      hGF hId hGF hId (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun _ hw ↦ by rw [LinearMap.add_apply, s.corrL_eq_zero_of_mem_filtration hw, add_zero])
      (AA.higherBarDifferential_filtration n ⟨z, hz, rfl⟩)]
  abel

private theorem Stage2Approx.barM_add_barDifferential {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) {z : ReducedTensorWords R A} (hz : z ∈ filtration R A (n + 1)) :
    gradedCoderivAlong (AA.grading.shift 1) 0
        ((f.barMap ∘ₗ d.homotopyInverse.barMap) ∘ₗ f.barMap) f.barMap (s.μ + s.corrM)
        (AA.barDifferential z) =
      s.barM (AA.barDifferential z) + ofLetter R B (s.corrM (AA.unaryBarDifferential z)) := by
  have hFGF := (f.isCoalgHom_barMap.comp d.homotopyInverse.isCoalgHom_barMap).comp
    f.isCoalgHom_barMap
  rw [Stage2Approx.barM, AA.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add,
    map_add, gradedCoderivAlong_add_apply_of_mem_filtration_succ (G := AA.grading.shift 1)
      hFGF f.isCoalgHom_barMap hFGF f.isCoalgHom_barMap (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun _ hw ↦ s.corrM_eq_zero_of_mem_filtration hw)
      (AA.unaryBarDifferential_filtration (n + 1) ⟨z, hz, rfl⟩),
    gradedCoderivAlong_apply_eq_of_mem_filtration (G := AA.grading.shift 1) (φ₂ := s.μ)
      hFGF f.isCoalgHom_barMap hFGF f.isCoalgHom_barMap (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun _ hw ↦ by rw [LinearMap.add_apply, s.corrM_eq_zero_of_mem_filtration hw, add_zero])
      (AA.higherBarDifferential_filtration n ⟨z, hz, rfl⟩)]
  abel

/-- Inductive step of Stage 2 (`n → n + 1`). -/
private noncomputable def stage2Step {d : f.LinearHomotopyInverse} {n : ℕ}
    (s : Stage2Approx d n) : Stage2Approx d (n + 1) where
  θ := s.θ + s.corrL
  hθ := s.hθ.add <| by
    rw [Stage2Approx.corrL]
    exact LinearMap.IsHomogeneous.sub
      (isHomogeneous_comp_of_eq (LinearMap.isHomogeneous_shift_piece_iff.2 d.isHomogeneous_inv)
        s.isHomogeneous_obsM)
      (isHomogeneous_comp_of_eq
        (LinearMap.isHomogeneous_shift_piece_iff.2 d.isHomogeneous_leftHomotopy)
        s.isHomogeneous_obsL)
  μ := s.μ + s.corrM
  hμ := s.hμ.add <| by
    rw [Stage2Approx.corrM]
    exact LinearMap.IsHomogeneous.add
      (LinearMap.IsHomogeneous.neg <|
        isHomogeneous_comp_of_eq
          (LinearMap.isHomogeneous_shift_piece_iff.2 d.isHomogeneous_rectifiedRightHomotopy)
          s.isHomogeneous_obsM)
      (isHomogeneous_comp_of_eq
        (LinearMap.isHomogeneous_shift_piece_iff.2 d.isHomogeneous_vogtHomotopy)
        s.isHomogeneous_obsL)
  vanishL z hz := by
    have hId := isCoalgHom_id (R := R) (M := A)
    have hGF := d.homotopyInverse.isCoalgHom_barMap.comp f.isCoalgHom_barMap
    have hLz := gradedCoderivAlong_add_apply_of_mem_filtration_succ (G := AA.grading.shift 1)
      (q := 1) (φ := s.θ) hGF hId hGF hId (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun _ hw ↦ s.corrL_eq_zero_of_mem_filtration hw) hz
    have hobs : s.errL z = ofLetter R A (s.obsL z) := by
      rw [s.errL_eq_ofLetter hz, Stage2Approx.obsL, LinearMap.comp_apply,
        apply_lengthProj_of_mem_filtration R A
          (fun _ hw ↦ by rw [LinearMap.comp_apply, s.errL_eq_zero hw, map_zero]) hz,
        LinearMap.comp_apply]
    have hkill := eq_sub_of_add_eq (s.kill_obsL z)
    rw [hLz, s.barL_add_barDifferential hz, map_add, AInfinityAlgebra.barDifferential_ofLetter,
      ← AInfinityAlgebra.differential_apply, hkill, map_sub, ← hobs]
    simp only [Stage2Approx.errL, Stage2Approx.barL, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.id_apply]
    abel
  vanishM z hz := by
    have hId := isCoalgHom_id (R := R) (M := A)
    have hGF := d.homotopyInverse.isCoalgHom_barMap.comp f.isCoalgHom_barMap
    have hFGF := (f.isCoalgHom_barMap.comp d.homotopyInverse.isCoalgHom_barMap).comp
      f.isCoalgHom_barMap
    have hLz := gradedCoderivAlong_add_apply_of_mem_filtration_succ (G := AA.grading.shift 1)
      (q := 1) (φ := s.θ) hGF hId hGF hId (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun _ hw ↦ s.corrL_eq_zero_of_mem_filtration hw) hz
    have hMz := gradedCoderivAlong_add_apply_of_mem_filtration_succ (G := AA.grading.shift 1)
      (q := 0) (φ := s.μ) hFGF f.isCoalgHom_barMap hFGF f.isCoalgHom_barMap
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun _ hw ↦ s.corrM_eq_zero_of_mem_filtration hw) hz
    have hobs : s.errM z = ofLetter R B (s.obsM z) := by
      rw [s.errM_eq_ofLetter hz, Stage2Approx.obsM, LinearMap.comp_apply,
        apply_lengthProj_of_mem_filtration R A
          (fun _ hw ↦ by rw [LinearMap.comp_apply, s.errM_eq_zero hw, map_zero]) hz,
        LinearMap.comp_apply]
    have hkill := eq_sub_of_add_eq' (eq_add_of_sub_eq (s.kill_obsM z))
    rw [hLz, hMz, s.barM_add_barDifferential hz, map_add, map_add, barMap_ofLetter,
      AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply, hkill,
      map_sub, map_add, ← hobs]
    simp only [Stage2Approx.errM, Stage2Approx.barL, Stage2Approx.barM, LinearMap.sub_apply,
      LinearMap.comp_apply]
    abel

private noncomputable def stage2Seq (d : f.LinearHomotopyInverse) :
    ∀ m : ℕ, Stage2Approx d (m + 1)
  | 0 => stage2Base d
  | m + 1 => stage2Step (stage2Seq d m)

private theorem stage2Seq_θ_stabilises (d : f.LinearHomotopyInverse) (m : ℕ)
    (z : ReducedTensorWords R A) (hz : z ∈ filtration R A (m + 1)) :
    (stage2Seq d (m + 1)).θ z = (stage2Seq d m).θ z := by
  rw [stage2Seq, stage2Step, LinearMap.add_apply,
    (stage2Seq d m).corrL_eq_zero_of_mem_filtration hz, add_zero]

/-- The lifted **left `A∞` homotopy** from `d.homotopyInverse.comp f` to `id AA`. -/
noncomputable def leftHomotopyLift (d : f.LinearHomotopyInverse) :
    Homotopy (d.homotopyInverse.comp f) (AInfinityHom.id AA) :=
  Homotopy.ofTaylor (stabilisingTaylor fun m ↦ (stage2Seq d m).θ)
    (isHomogeneous_stabilisingTaylor (stage2Seq_θ_stabilises d) fun m ↦ (stage2Seq d m).hθ)
    (LinearMap.ext fun z ↦ by
      obtain ⟨m, hm⟩ := exists_mem_filtration R A z
      have hz : z ∈ filtration R A (m + 1) := filtration_monotone R A m.le_succ hm
      have hGF : IsCoalgHom R (d.homotopyInverse.barMap ∘ₗ f.barMap) :=
        d.homotopyInverse.isCoalgHom_barMap.comp f.isCoalgHom_barMap
      have hId := isCoalgHom_id (R := R) (M := A)
      have hL : gradedCoderivAlong (AA.grading.shift 1) 1 (d.homotopyInverse.barMap ∘ₗ f.barMap)
          LinearMap.id (stabilisingTaylor fun k ↦ (stage2Seq d k).θ) z =
          (stage2Seq d m).barL z := by
        rw [Stage2Approx.barL]
        exact gradedCoderivAlong_apply_eq_of_mem_filtration (G := AA.grading.shift 1)
          (φ₂ := (stage2Seq d m).θ) hGF hId hGF hId (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
          (fun _ hw ↦ stabilisingTaylor_apply_of_mem_filtration (stage2Seq_θ_stabilises d) hw) hz
      have hv := congrArg (letter R A) ((stage2Seq d m).vanishL z hz)
      have hl₁ := LinearMap.congr_fun AA.letter_comp_barDifferential ((stage2Seq d m).barL z)
      have hl₂ := LinearMap.congr_fun (letter_comp_gradedCoderivAlong (AA.grading.shift 1) 1
        (d.homotopyInverse.barMap ∘ₗ f.barMap) LinearMap.id (stage2Seq d m).θ)
        (AA.barDifferential z)
      rw [LinearMap.comp_apply, Stage2Approx.barL] at hl₁
      rw [LinearMap.comp_apply] at hl₂
      rw [map_sub, map_add, hl₁, hl₂] at hv
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
        AInfinityHom.taylor_def, barMap_comp, barMap_id, LinearMap.id_apply]
      rw [hL, Stage2Approx.barL, stabilisingTaylor_apply_of_mem_filtration
          (stage2Seq_θ_stabilises d) (AA.barDifferential_mem_filtration hz)]
      exact hv)

/-- The arity-one component of `d.leftHomotopyLift` is `d.leftHomotopy`. -/
@[simp]
theorem linearHomotopy_leftHomotopyLift (d : f.LinearHomotopyInverse) :
    d.leftHomotopyLift.linearHomotopy = d.leftHomotopy :=
  LinearMap.ext fun a ↦ by
    rw [leftHomotopyLift, Homotopy.linearHomotopy_ofTaylor, LinearMap.comp_apply,
      stabilisingTaylor_apply_of_mem_filtration (stage2Seq_θ_stabilises d)
        (ofLetter_mem_filtration R A a), stage2Seq, stage2Base, LinearMap.comp_apply,
      letter_ofLetter]

/-- Symmetry of linear chain-homotopy inverses via the lifted two-sided `A∞` homotopies. -/
noncomputable def symm {f : AInfinityHom AA BB} (d : f.LinearHomotopyInverse) :
    d.homotopyInverse.LinearHomotopyInverse :=
  Homotopy.toLinearHomotopyInverse d.rightHomotopyLift d.leftHomotopyLift

end Stage2

end LinearHomotopyInverse

end AInfinityHom

end TauCeti
