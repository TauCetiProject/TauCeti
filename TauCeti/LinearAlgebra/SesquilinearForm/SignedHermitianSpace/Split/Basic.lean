/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.Isometry
import TauCeti.RingTheory.Artinian.Module

/-!
# Signed hermitian spaces over the split quadratic algebra `F × F`

Let `F` be a field and `E = F × F` the split quadratic étale `F`-algebra, with the involution
`σ (a, b) = (b, a)` exchanging the factors. (This is not Mathlib's componentwise `star` on a
product, which is why the involution is an explicit ring homomorphism.) Over `E`, signed hermitian
spaces have no invariant besides their rank: a finite free `ε`-hermitian space `(V, h)` of rank `n`
is isometric to `E^n` with the form `h a b = ∑ σ (a i) * (ε, 1) * b i`
(`TauCeti.SignedHermitianSpace.exists_linearEquiv_form_eq_sum_split`), so any two of the same
rank are isometric (`TauCeti.SignedHermitianSpace.equivalent_of_finrank_eq_split`). Witt
cancellation over `E` follows by counting ranks
(`TauCeti.SignedHermitianSpace.equivalent_of_equivalent_prod_split`). For `ε = 1` the model is
the standard form `∑ σ (a i) * b i`.

The proof uses the idempotents `e₁ = (1, 0)` and `e₂ = (0, 1)`, which `σ` exchanges, so that
`h (e₁ x) (e₁ y) = e₂ e₁ h x y = 0`: the summands `e₁ V` and `e₂ V` are totally isotropic, and `h`
pairs them perfectly. For a basis `cᵢ` of `V`, choose `dⱼ` with `h cᵢ dⱼ = δᵢⱼ`; then the vectors
`fᵢ = e₁ cᵢ + e₂ dᵢ` satisfy `h fᵢ fⱼ = δᵢⱼ (ε, 1)`. The vectors `dⱼ` exist, and the `fᵢ` form a
basis, because an injective linear map between free `E`-modules of the same finite rank is
bijective (`E` is artinian, `IsArtinian.bijective_of_injective_of_linearEquiv`).

## Main statements

* `TauCeti.SignedHermitianSpace.exists_linearEquiv_form_eq_sum_split`: the diagonal model.
* `TauCeti.SignedHermitianSpace.equivalent_of_finrank_eq_split`: classification by the rank.
* `TauCeti.SignedHermitianSpace.equivalent_of_equivalent_prod_split`: Witt cancellation over
  `F × F`.

## References

* W. Scharlau, *Quadratic and Hermitian Forms*, Grundlehren der mathematischen Wissenschaften
  270, Springer (1985), Chapter 7.
-/

public section

open Module

namespace TauCeti

namespace SignedHermitianSpace

variable {F V : Type*} [Field F] [AddCommGroup V] [Module (F × F) V] [Module.Free (F × F) V]
  [Module.Finite (F × F) V] {σ : F × F →+* F × F} {ε : ℤˣ}
  (H : SignedHermitianSpace (F × F) V σ ε)

omit [Module.Free (F × F) V] [Module.Finite (F × F) V] in
include H in
/-- A vector paired to `0` with every vector of a basis is `0`. -/
private theorem eq_zero_of_forall_basis {ι : Type*} (c : Basis ι (F × F) V) {d : V}
    (hd : ∀ i, H.form (c i) d = 0) : d = 0 :=
  H.separatingRight d fun x ↦ by
    have : H.form.flip d = 0 := c.ext fun i ↦ by simpa using hd i
    simpa using LinearMap.congr_fun this x

omit [Module.Free (F × F) V] in
/-- For a basis `c`, the vectors `dⱼ` with `h cᵢ dⱼ = δᵢⱼ`. -/
private theorem exists_form_apply_eq_ite_split {n : ℕ} (c : Basis (Fin n) (F × F) V) (j : Fin n) :
    ∃ d, ∀ i, H.form (c i) d = if i = j then 1 else 0 := by
  let Φ : V →ₗ[F × F] Fin n → F × F := LinearMap.pi fun i ↦ H.form (c i)
  have hΦ : Function.Injective Φ := (injective_iff_map_eq_zero Φ).2 fun d hd ↦
    H.eq_zero_of_forall_basis c fun i ↦ congrFun hd i
  obtain ⟨d, hd⟩ :=
    (IsArtinian.bijective_of_injective_of_linearEquiv c.equivFun Φ hΦ).2 (Pi.single j 1)
  exact ⟨d, fun i ↦ by simpa [Φ, Pi.single_apply] using congrFun hd i⟩

/-- **The diagonal model of a space over `F × F`.** Let `σ` be the involution `(a, b) ↦ (b, a)` of
`F × F`. A finite free `ε`-hermitian space `(V, h)` over `F × F` of rank `n` is isometric to
`(F × F)ⁿ` with the form `∑ σ (a i) * (ε, 1) * b i`. -/
theorem exists_linearEquiv_form_eq_sum_split (hσ : ∀ x, σ x = x.swap) {n : ℕ}
    (hn : finrank (F × F) V = n) :
    ∃ T : (Fin n → F × F) ≃ₗ[F × F] V, ∀ a b,
      H.form (T a) (T b) = ∑ i, σ (a i) * (((ε : ℤ) : F), 1) * b i := by
  let c : Basis (Fin n) (F × F) V := (Module.finBasis (F × F) V).reindex (finCongr hn)
  choose d hd using H.exists_form_apply_eq_ite_split c
  let e₁ : F × F := (1, 0)
  let e₂ : F × F := (0, 1)
  let f : Fin n → V := fun i ↦ e₁ • c i + e₂ • d i
  have hσe₁ : σ e₁ = e₂ := by simp [hσ, e₁, e₂]
  have hσe₂ : σ e₂ = e₁ := by simp [hσ, e₁, e₂]
  -- The Gram matrix of `f` is `(ε, 1)` times the identity.
  have hf (i j : Fin n) : H.form (f i) (f j) = if i = j then (((ε : ℤ) : F), 1) else 0 := by
    have hdc : H.form (d i) (c j) = ε • σ (H.form (c j) (d i)) := H.form_swap (c j) (d i)
    simp only [f, map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hσe₁, hσe₂, hd, hdc]
    rw [RingHom.id_apply, RingHom.id_apply]
    by_cases hij : i = j
    · subst hij
      ext <;> simp [e₁, e₂, hσ, Units.smul_def, zsmul_eq_mul]
    · ext <;> simp [e₁, e₂, hij, Ne.symm hij]
  let T : (Fin n → F × F) →ₗ[F × F] V := Fintype.linearCombination (F × F) f
  have hT (a : Fin n → F × F) : T a = ∑ i, a i • f i := by
    simp [T, Fintype.linearCombination_apply]
  have hTf (a b : Fin n → F × F) :
      H.form (T a) (T b) = ∑ i, σ (a i) * (((ε : ℤ) : F), 1) * b i := by
    simp only [hT, map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      hf]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [RingHom.id_apply, Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
    simp only [ite_true]
    ring
  -- `T` is injective since the Gram matrix is invertible, hence bijective.
  have hinj : Function.Injective T := (injective_iff_map_eq_zero T).2 fun a ha ↦ funext fun j ↦ by
    have h := congrArg (fun v ↦ H.form (f j) v) ha
    simp only [hT, map_sum, map_smul, smul_eq_mul, hf, mul_ite, mul_zero, map_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
    have hu : IsUnit ((((ε : ℤ) : F), (1 : F)) : F × F) :=
      Prod.isUnit_iff.2 ⟨(ε.isUnit.map (Int.castRingHom F)), isUnit_one⟩
    exact hu.mul_left_eq_zero.1 h
  exact ⟨LinearEquiv.ofBijective T
    (IsArtinian.bijective_of_injective_of_linearEquiv c.equivFun.symm T hinj), hTf⟩

/-- **Classification over `F × F`.** Let `σ` be the involution `(a, b) ↦ (b, a)` of `F × F`. Two
finite free `ε`-hermitian spaces over `F × F` of the same rank are isometric. -/
theorem equivalent_of_finrank_eq_split {V' : Type*} [AddCommGroup V'] [Module (F × F) V']
    [Module.Free (F × F) V'] [Module.Finite (F × F) V'] (hσ : ∀ x, σ x = x.swap)
    (H' : SignedHermitianSpace (F × F) V' σ ε) (h : finrank (F × F) V = finrank (F × F) V') :
    Equivalent H H' := by
  obtain ⟨T, hT⟩ := H.exists_linearEquiv_form_eq_sum_split hσ h
  obtain ⟨T', hT'⟩ := H'.exists_linearEquiv_form_eq_sum_split hσ rfl
  refine IsometryEquiv.equivalent { T.symm.trans T' with map_app' := fun x y ↦ ?_ }
  simp only [LinearEquiv.toFun_eq_coe, LinearEquiv.trans_apply, hT']
  rw [← hT, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- **Witt cancellation over `F × F`.** Let `σ` be the involution `(a, b) ↦ (b, a)` of `F × F`.
For finite free `ε`-hermitian spaces over `F × F`, `U ⊥ V ≅ U ⊥ V'` implies `V ≅ V'`. -/
theorem equivalent_of_equivalent_prod_split {V₀ V' : Type*} [AddCommGroup V₀]
    [Module (F × F) V₀] [Module.Free (F × F) V₀] [Module.Finite (F × F) V₀] [AddCommGroup V']
    [Module (F × F) V'] [Module.Free (F × F) V'] [Module.Finite (F × F) V']
    (hσ : ∀ x, σ x = x.swap) {H₀ : SignedHermitianSpace (F × F) V₀ σ ε}
    {H' : SignedHermitianSpace (F × F) V' σ ε} (h : Equivalent (H₀.prod H) (H₀.prod H')) :
    Equivalent H H' := by
  obtain ⟨e⟩ := h.nonempty
  have := e.toLinearEquiv.finrank_eq
  rw [finrank_prod, finrank_prod] at this
  exact H.equivalent_of_finrank_eq_split hσ H' (by lia)

end SignedHermitianSpace

end TauCeti
