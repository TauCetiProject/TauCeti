/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import TauCeti.LinearAlgebra.Unimodular.Polynomial
import Mathlib.RingTheory.Localization.Algebra
import TauCeti.RingTheory.Localization.IntegerMultiple

/-!
# Quillen patching and Horrocks' theorem over an integral domain

Let `B` be an integral domain and `f : ι → B[X]` a vector of polynomials. Quillen's patching
theorem says that `f` is equivalent to the vector `f(0)` of its constant terms as soon as this
holds after localising at every maximal ideal `𝔪` of `B`, over `B_𝔪[X]`
(`TauCeti.unimodularEquiv_C_eval_zero_of_forall_isMaximal`). Combined with Horrocks' theorem over
a local ring (`TauCeti.unimodularEquiv_C_eval_zero_of_isLocalRing`), this gives Horrocks' theorem
over an integral domain: a unimodular vector over `B[X]` with a monic entry is equivalent to the
vector of its constant terms (`TauCeti.unimodularEquiv_C_eval_zero_of_monic`). This is the
inductive step of the Quillen–Suslin theorem, and of its rigid-analytic analogue over
Monsky–Washnitzer algebras, where a unimodular vector is first moved, by a change of coordinates
and Weierstrass preparation, to one with polynomial entries and a monic entry.

## The patching argument

Write `Y` for a second variable. The set `J` of `c ∈ B` such that `f(X)` and `f(X + cY)` are
equivalent over `B[X][Y]` is an ideal: it contains `0`, substituting `Y ↦ bY` shows `c ∈ J ⇒
bc ∈ J`, and substituting `X ↦ X + cY` into an equivalence `f(X) ∼ f(X + dY)` and composing with
`f(X) ∼ f(X + cY)` gives `c + d ∈ J`.

For a maximal ideal `𝔪`, let `M ∈ GL(B_𝔪[X])` carry `f` to `f(0)`. Then
`G = M(X + Y)⁻¹ M(X)` carries `f(X)` to `f(X + Y)` and `G(X, 0) = 1`. Because the entries of
`G - 1` are divisible by `Y`, clearing denominators gives `s ∉ 𝔪` such that `G(X, sY)` and its
inverse have entries in `B[X][Y]`; here `B[X][Y] ⊆ B_𝔪[X][Y]` because `B` is a domain. Then
`G(X, sY)` carries `f(X)` to `f(X + sY)` over `B[X][Y]`, so `s ∈ J`. As `J` lies in no maximal
ideal, `1 ∈ J`, and substituting `X ↦ 0, Y ↦ X` in `f(X) ∼ f(X + Y)` gives `f(0) ∼ f`.

Quillen's patching theorem holds over every commutative ring; the formalization here uses that
the localisation maps of a domain are injective, as in Lang's proof.

## Main results

* `TauCeti.unimodularEquiv_C_eval_zero_of_forall_isMaximal`: Quillen patching over an integral
  domain.
* `TauCeti.unimodularEquiv_C_eval_zero_of_isUnit_leadingCoeff`,
  `TauCeti.unimodularEquiv_C_eval_zero_of_monic`: Horrocks' theorem over an integral domain.

## References

* S. Lang, *Algebra*, 3rd ed., GTM 211, Springer, 2002, Chapter XXI, §3, Theorem 3.4.
* D. Quillen, *Projective modules over polynomial rings*, Invent. Math. 36 (1976), 167–171.
* T. Y. Lam, *Serre's Problem on Projective Modules*, Springer, 2006, Chapter VI, §1.
-/

public section

noncomputable section

open Module Polynomial
open scoped Matrix

namespace TauCeti

variable {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι] [DecidableEq ι]

/-! ### Substitutions in two variables

We write `R[X][X]` for the polynomials in two variables, with outer variable `Y = X` and inner
variable `C X`. -/

/-- The substitution `p(X) ↦ p(X + cY)`, from `R[X]` to `R[X][Y]`. -/
private def shift (c : R) : R[X] →+* R[X][X] :=
  eval₂RingHom (C.comp C) (C X + C (C c) * X)

/-- The substitution `p(X, Y) ↦ p(X, cY)` on `R[X][Y]`. -/
private def scale (c : R) : R[X][X] →+* R[X][X] :=
  eval₂RingHom C (C (C c) * X)

/-- The substitution `p(X, Y) ↦ p(X + cY, Y)` on `R[X][Y]`. -/
private def shiftY (c : R) : R[X][X] →+* R[X][X] :=
  eval₂RingHom (shift c) X

/-- The substitution `p(X, Y) ↦ p(0, X)`, from `R[X][Y]` to `R[X]`. -/
private def diag : R[X][X] →+* R[X] :=
  eval₂RingHom (C.comp (evalRingHom 0)) X

private theorem shift_C (c a : R) : shift c (C a) = C (C a) :=
  eval₂_C _ _

private theorem shift_X (c : R) : shift c X = C X + C (C c) * X :=
  eval₂_X _ _

private theorem scale_C (c : R) (p : R[X]) : scale c (C p) = C p :=
  eval₂_C _ _

private theorem scale_X (c : R) : scale c X = C (C c) * X :=
  eval₂_X _ _

private theorem shiftY_C (c : R) (p : R[X]) : shiftY c (C p) = shift c p :=
  eval₂_C _ _

private theorem shiftY_X (c : R) : shiftY c X = X :=
  eval₂_X _ _

private theorem diag_C (p : R[X]) : diag (C p) = C (p.eval 0) :=
  eval₂_C _ _

private theorem diag_X : diag (X : R[X][X]) = X :=
  eval₂_X _ _

private theorem shift_zero (p : R[X]) : shift 0 p = C p := by
  refine RingHom.congr_fun (f := shift 0) (g := C) (ringHom_ext (fun a ↦ ?_) ?_) p
  · simp [shift_C]
  · simp [shift_X]

private theorem shiftY_shift (c d : R) (p : R[X]) : shiftY c (shift d p) = shift (c + d) p := by
  refine RingHom.congr_fun (f := (shiftY c).comp (shift d)) (ringHom_ext (fun a ↦ ?_) ?_) p
  · simp [shift_C, shiftY_C]
  · simp only [RingHom.comp_apply, shift_X, map_add, map_mul, shiftY_C, shiftY_X, shift_C]
    ring

private theorem scale_shift (b c : R) (p : R[X]) : scale b (shift c p) = shift (b * c) p := by
  refine RingHom.congr_fun (f := (scale b).comp (shift c)) (ringHom_ext (fun a ↦ ?_) ?_) p
  · simp [shift_C, scale_C]
  · simp only [RingHom.comp_apply, shift_X, map_add, map_mul, scale_C, scale_X]
    ring

private theorem eval_zero_shift (c : R) (p : R[X]) : (shift c p).eval 0 = p := by
  refine RingHom.congr_fun (f := (evalRingHom 0).comp (shift c)) (g := RingHom.id _)
    (ringHom_ext (fun a ↦ ?_) ?_) p
  · simp [shift_C]
  · simp [shift_X]

private theorem diag_shift_one (p : R[X]) : diag (shift 1 p) = p := by
  refine RingHom.congr_fun (f := diag.comp (shift 1)) (g := RingHom.id _)
    (ringHom_ext (fun a ↦ ?_) ?_) p
  · simp [shift_C, diag_C]
  · simp [shift_X, diag_C, diag_X]

private theorem map_map_shift (φ : R →+* S) (c : R) (p : R[X]) :
    (shift c p).map (mapRingHom φ) = shift (φ c) (p.map φ) := by
  refine RingHom.congr_fun (f := (mapRingHom (mapRingHom φ)).comp (shift c))
    (g := (shift (φ c)).comp (mapRingHom φ)) (ringHom_ext (fun a ↦ ?_) ?_) p
  · simp [shift_C]
  · simp [shift_X]

private theorem map_map_scale (φ : R →+* S) (c : R) (p : R[X][X]) :
    (scale c p).map (mapRingHom φ) = scale (φ c) (p.map (mapRingHom φ)) := by
  refine RingHom.congr_fun (f := (mapRingHom (mapRingHom φ)).comp (scale c))
    (g := (scale (φ c)).comp (mapRingHom (mapRingHom φ))) (ringHom_ext (fun a ↦ ?_) ?_) p
  · simp [scale_C]
  · simp [scale_X]

/-! ### The patching ideal -/

/-- The ideal of `c` such that `f(X)` and `f(X + cY)` are equivalent over `R[X][Y]`. -/
private def patchingIdeal (f : ι → R[X]) : Ideal R where
  carrier := {c | UnimodularEquiv (fun k ↦ C (f k)) (fun k ↦ shift c (f k))}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, shift_zero]
    exact .rfl
  add_mem' {c d} hc hd := by
    have h := UnimodularEquiv.map (shiftY c) hd
    simp only [Function.comp_def, shiftY_C, shiftY_shift] at h
    exact (hc : UnimodularEquiv _ _).trans h
  smul_mem' b c hc := by
    have h := UnimodularEquiv.map (scale b) hc
    simp only [Function.comp_def, scale_C, scale_shift] at h
    exact h

private theorem mem_patchingIdeal {f : ι → R[X]} {c : R} :
    c ∈ patchingIdeal f ↔ UnimodularEquiv (fun k ↦ C (f k)) (fun k ↦ shift c (f k)) :=
  Iff.rfl

/-! ### Clearing denominators -/

private theorem map_map_injective {φ : R →+* S} (hφ : Function.Injective φ) :
    Function.Injective (Polynomial.map (mapRingHom φ)) :=
  map_injective _ (by rw [coe_mapRingHom]; exact map_injective _ hφ)

section Localization

variable {M : Submonoid R} [Algebra R S] [IsLocalization M S]

attribute [local instance] Polynomial.algebra in
/-- A finite family of polynomials in two variables over a localisation `S` of `R` becomes a
family of polynomials over `R` after multiplication by a single element of `M`: clear the
denominators over the localisation `S[X]` of `R[X]` (`Polynomial.isLocalization`). -/
private theorem exists_map_map_eq_mul {κ : Type*} [Finite κ] (q : κ → S[X][X]) :
    ∃ s ∈ M, ∀ k, ∃ q' : R[X][X],
      q'.map (mapRingHom (algebraMap R S)) = C (C (algebraMap R S s)) * q k := by
  have := Polynomial.isLocalization M S
  obtain ⟨⟨_, s, hs, rfl⟩, hq⟩ := IsLocalization.exists_polynomial_map_eq_smul (M.map C) q
  refine ⟨s, hs, fun k ↦ ?_⟩
  obtain ⟨q', hq'⟩ := hq k
  refine ⟨q', ?_⟩
  rw [← Polynomial.algebraMap_def, hq', ← algebraMap_smul S[X] (C s), smul_eq_C_mul]
  simp

/-- If the constant terms in `Y` of the entries of a matrix over `S[X][Y]` come from `R[X]`,
then for some `s ∈ M` and every `u` the matrix `A(X, suY)` comes from `R[X][Y]`. -/
private theorem exists_mapMatrix_eq_scale (A : Matrix ι ι S[X][X])
    (hA : ∀ i j, (A i j).coeff 0 ∈ Set.range (Polynomial.map (algebraMap R S))) :
    ∃ s ∈ M, ∀ u : R, ∃ A' : Matrix ι ι R[X][X],
      (mapRingHom (mapRingHom (algebraMap R S))).mapMatrix A' =
        (scale (algebraMap R S (s * u))).mapMatrix A := by
  choose a ha using hA
  obtain ⟨s, hs, hq⟩ := exists_map_map_eq_mul (M := M) fun ij : ι × ι ↦ (A ij.1 ij.2).divX
  choose q hq using hq
  refine ⟨s, hs, fun u ↦
    ⟨Matrix.of fun i j ↦ C (C u) * X * scale (s * u) (q (i, j)) + C (a i j), ?_⟩⟩
  -- `A = Y A' + A(X, 0)`, and `s A'` comes from `R[X][Y]`.
  ext i j : 1
  conv_rhs => rw [RingHom.mapMatrix_apply, Matrix.map_apply, ← X_mul_divX_add (A i j)]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Polynomial.map_add,
    Polynomial.map_mul, map_C, coe_mapRingHom, map_X, map_map_scale, hq, map_add, map_mul,
    scale_X, scale_C, ha]
  ring

/-- An invertible matrix `G` over `S[X][Y]` with `G(X, 0) = 1` has, for some `s ∈ M`, the
matrix `G(X, sY)` coming from an invertible matrix over `R[X][Y]`, provided `R → S` is injective.
-/
private theorem exists_map_eq_scale (hinj : Function.Injective (algebraMap R S))
    (G : GL ι S[X][X]) (hG : Matrix.GeneralLinearGroup.map (evalRingHom 0) G = 1) :
    ∃ s ∈ M, ∃ P : GL ι R[X][X],
      Matrix.GeneralLinearGroup.map (mapRingHom (mapRingHom (algebraMap R S))) P =
        Matrix.GeneralLinearGroup.map (scale (algebraMap R S s)) G := by
  -- The entries of `G` and `G⁻¹` have constant terms `0` or `1` in `Y`.
  have hcoeff : ∀ H : GL ι S[X][X], Matrix.GeneralLinearGroup.map (evalRingHom 0) H = 1 →
      ∀ i j, ((H : Matrix ι ι S[X][X]) i j).coeff 0 ∈
        Set.range (Polynomial.map (algebraMap R S)) := fun H hH i j ↦ by
    have := congr_arg (fun H : GL ι S[X] ↦ (H : Matrix ι ι S[X]) i j) hH
    simp only [Matrix.GeneralLinearGroup.map_apply, coe_evalRingHom,
      Matrix.GeneralLinearGroup.coe_one] at this
    rw [coeff_zero_eq_eval_zero, this]
    exact ⟨(1 : Matrix ι ι R[X]) i j, by simp only [Matrix.one_apply]; split_ifs <;> simp⟩
  obtain ⟨s, hs, hP⟩ := exists_mapMatrix_eq_scale (M := M) _ (hcoeff G hG)
  obtain ⟨t, ht, hQ⟩ := exists_mapMatrix_eq_scale (M := M) _
    (hcoeff G⁻¹ (by rw [map_inv, hG, inv_one]))
  obtain ⟨P, hP⟩ := hP t
  obtain ⟨Q, hQ⟩ := hQ s
  rw [mul_comm t s] at hQ
  have hinj' : Function.Injective ((mapRingHom (mapRingHom (algebraMap R S))).mapMatrix :
      Matrix ι ι R[X][X] → Matrix ι ι S[X][X]) :=
    Matrix.map_injective (map_map_injective hinj)
  have hPQ : ∀ (G' : GL ι S[X][X]) (P' Q' : Matrix ι ι R[X][X]),
      (mapRingHom (mapRingHom (algebraMap R S))).mapMatrix P' =
        (scale (algebraMap R S (s * t))).mapMatrix G' →
      (mapRingHom (mapRingHom (algebraMap R S))).mapMatrix Q' =
        (scale (algebraMap R S (s * t))).mapMatrix ↑G'⁻¹ → P' * Q' = 1 :=
    fun G' P' Q' hP' hQ' ↦ hinj' (by rw [map_mul, hP', hQ']; simp)
  refine ⟨s * t, mul_mem hs ht, ⟨P, Q, hPQ G P Q hP hQ, ?_⟩, Units.ext hP⟩
  refine hPQ G⁻¹ Q P hQ ?_
  rwa [inv_inv]

end Localization

/-- If `N` carries `g` to the vector `g(0)` of its constant terms over `S[X]`, then
`G = N(X + Y)⁻¹ N(X)` carries `g(X)` to `g(X + Y)` over `S[X][Y]`, and `G(X, 0) = 1`. -/
private theorem exists_mulVec_eq_shift_one {g : ι → S[X]}
    (hg : UnimodularEquiv g (fun k ↦ C ((g k).eval 0))) :
    ∃ G : GL ι S[X][X], (G : Matrix ι ι S[X][X]) *ᵥ (fun k ↦ C (g k)) = (fun k ↦ shift 1 (g k)) ∧
      Matrix.GeneralLinearGroup.map (evalRingHom 0) G = 1 := by
  obtain ⟨N, hN⟩ := unimodularEquiv_iff.mp hg
  refine ⟨Matrix.GeneralLinearGroup.map (shift 1) N⁻¹ * Matrix.GeneralLinearGroup.map C N, ?_, ?_⟩
  · have hNinv : (↑N⁻¹ : Matrix ι ι S[X]) *ᵥ (fun k ↦ C ((g k).eval 0)) = g := by
      simp [← hN, Matrix.mulVec_mulVec]
    have hCN : ((Matrix.GeneralLinearGroup.map C N : GL ι S[X][X]) : Matrix ι ι S[X][X]) *ᵥ
        (fun k ↦ C (g k)) = shift 1 ∘ fun k ↦ C ((g k).eval 0) := by
      funext k
      rw [Function.comp_apply, shift_C, ← congr_fun hN k]
      simp [RingHom.map_mulVec, Function.comp_def]
    rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hCN,
      Matrix.GeneralLinearGroup.val_map_apply]
    funext k
    rw [← RingHom.map_mulVec, hNinv]
  · have h₁ : (evalRingHom 0).comp (shift (1 : S)) = RingHom.id _ :=
      RingHom.ext fun p ↦ eval_zero_shift 1 p
    have h₂ : (evalRingHom 0).comp (C : S[X] →+* S[X][X]) = RingHom.id _ :=
      RingHom.ext fun p ↦ eval_C
    simp only [map_mul, ← MonoidHom.comp_apply, ← Matrix.GeneralLinearGroup.map_comp, h₁, h₂,
      Matrix.GeneralLinearGroup.map_id, MonoidHom.id_apply, inv_mul_cancel]

/-- The local step of the patching argument: if `f` is equivalent to `f(0)` over `S[X]` for a
localisation `S` of `R` at `M` with `R → S` injective, then the patching ideal of `f` meets `M`.
-/
private theorem exists_mem_patchingIdeal {M : Submonoid R} [Algebra R S] [IsLocalization M S]
    (hinj : Function.Injective (algebraMap R S)) {f : ι → R[X]}
    (hf : UnimodularEquiv (fun k ↦ (f k).map (algebraMap R S))
      (fun k ↦ C (((f k).map (algebraMap R S)).eval 0))) :
    ∃ s ∈ M, s ∈ patchingIdeal f := by
  obtain ⟨G, hG, hG0⟩ := exists_mulVec_eq_shift_one hf
  obtain ⟨s, hs, P, hP⟩ := exists_map_eq_scale (M := M) hinj G hG0
  refine ⟨s, hs, mem_patchingIdeal.mpr <| unimodularEquiv_iff.mpr
    ⟨P, funext fun k ↦ map_map_injective hinj ?_⟩⟩
  -- Over `S[X][Y]` the matrix `P` becomes `G(X, sY)`, which carries `f(X)` to `f(X + sY)`.
  have hPval := congr_arg (fun H : GL ι S[X][X] ↦ (H : Matrix ι ι S[X][X])) hP
  simp only [Matrix.GeneralLinearGroup.val_map_apply] at hPval
  have h := RingHom.map_mulVec (mapRingHom (mapRingHom (algebraMap R S)))
    (P : Matrix ι ι R[X][X]) (fun k ↦ C (f k)) k
  rw [coe_mapRingHom] at h hPval
  rw [h, hPval, map_map_shift]
  have hC : (Polynomial.map (mapRingHom (algebraMap R S)) ∘ fun k ↦ C (f k)) =
      ⇑(scale (algebraMap R S s)) ∘ fun k ↦ C ((f k).map (algebraMap R S)) := by
    funext k
    simp [scale_C]
  rw [hC, ← RingHom.map_mulVec, hG]
  simp [scale_shift]

/-! ### Quillen patching and Horrocks' theorem -/

/-- **Quillen patching** over an integral domain: a vector of polynomials `f : ι → R[X]` is
equivalent to the vector `f(0)` of its constant terms as soon as this holds over `R_𝔪[X]` for
every maximal ideal `𝔪` of `R`. -/
theorem unimodularEquiv_C_eval_zero_of_forall_isMaximal [IsDomain R] {f : ι → R[X]}
    (h : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal],
      UnimodularEquiv (fun k ↦ (f k).map (algebraMap R (Localization.AtPrime 𝔪)))
        (fun k ↦ C (((f k).map (algebraMap R (Localization.AtPrime 𝔪))).eval 0))) :
    UnimodularEquiv f (fun k ↦ C ((f k).eval 0)) := by
  -- The patching ideal lies in no maximal ideal, so it contains `1`.
  have hJ : patchingIdeal f = ⊤ := by
    by_contra hJ
    obtain ⟨𝔪, h𝔪, hJ𝔪⟩ := Ideal.exists_le_maximal _ hJ
    obtain ⟨s, hs, hsJ⟩ := exists_mem_patchingIdeal (M := 𝔪.primeCompl)
      (IsLocalization.injective (Localization.AtPrime 𝔪) 𝔪.primeCompl_le_nonZeroDivisors) (h 𝔪)
    exact hs (hJ𝔪 hsJ)
  have h1 : (1 : R) ∈ patchingIdeal f := hJ ▸ Submodule.mem_top
  -- Substitute `X ↦ 0, Y ↦ X` in `f(X) ∼ f(X + Y)`.
  have h := UnimodularEquiv.map diag (mem_patchingIdeal.mp h1)
  simp only [Function.comp_def, diag_C, diag_shift_one] at h
  exact h.symm

/-- **Horrocks' theorem** over an integral domain `R`: a unimodular vector of polynomials
`f : ι → R[X]` one of whose entries has a unit leading coefficient is equivalent to the vector
`f(0)` of its constant terms. -/
theorem unimodularEquiv_C_eval_zero_of_isUnit_leadingCoeff [IsDomain R] {f : ι → R[X]}
    (hf : IsUnimodular R[X] f) {i : ι} (hi : IsUnit (f i).leadingCoeff) :
    UnimodularEquiv f (fun k ↦ C ((f k).eval 0)) := by
  refine unimodularEquiv_C_eval_zero_of_forall_isMaximal fun 𝔪 _ ↦ ?_
  have hlc : ((f i).map (algebraMap R (Localization.AtPrime 𝔪))).leadingCoeff =
      algebraMap R _ (f i).leadingCoeff :=
    leadingCoeff_map_of_leadingCoeff_ne_zero _ (hi.map _).ne_zero
  exact unimodularEquiv_C_eval_zero_of_isLocalRing
    (hf.ringHom_comp (mapRingHom (algebraMap R (Localization.AtPrime 𝔪)))) (i := i)
    (hlc ▸ hi.map _)

/-- **Horrocks' theorem** over an integral domain `R`, monic form: a unimodular vector of
polynomials `f : ι → R[X]` with a monic entry is equivalent to the vector `f(0)` of its constant
terms. -/
theorem unimodularEquiv_C_eval_zero_of_monic [IsDomain R] {f : ι → R[X]}
    (hf : IsUnimodular R[X] f) {i : ι} (hi : (f i).Monic) :
    UnimodularEquiv f (fun k ↦ C ((f k).eval 0)) :=
  unimodularEquiv_C_eval_zero_of_isUnit_leadingCoeff hf (hi.leadingCoeff ▸ isUnit_one)

end TauCeti
