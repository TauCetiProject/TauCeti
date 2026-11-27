/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.CoalgHom
public import TauCeti.LinearAlgebra.TensorCoalgebra.Conilpotence

/-!
# The reduced tensor coalgebra is cofree among conilpotent coalgebras

Let `Δ : C ⟶ C ⊗ C` be a coassociative conilpotent coproduct (`LinearMap.IsConilpotent`), the
structure carried by the coaugmentation coideal of a coaugmented conilpotent coalgebra. For every
module `N`, coalgebra maps `F : C ⟶ Tᶜ(N)` into the reduced tensor coalgebra
`Tᶜ(N) = ⨁_{n ≥ 1} N^{⊗n}` with reduced deconcatenation, that is linear maps with
`Δ_{Tᶜ(N)} ∘ F = (F ⊗ F) ∘ Δ`, correspond bijectively to linear maps `f : C ⟶ N`
(`LinearMap.IsConilpotent.coalgHomEquiv`). The map `F` is recovered from `f` as the *cofree lift*

`F c = ∑_{n ≥ 0} f^{⊗(n + 1)} (Δ⁽ⁿ⁾ c)`,

whose length-`(n + 1)` component is `f^{⊗(n + 1)} ∘ Δ⁽ⁿ⁾`, where `Δ⁽ⁿ⁾` is the iterated coproduct
`LinearMap.iteratedComul`. The sum is finite on each element exactly because `Δ` is conilpotent.
Conversely `f` is the composite of `F` with the projection `Tᶜ(N) ⟶ N` onto single letters.

That `F` is a coalgebra map is generalized coassociativity (`LinearMap.iteratedComul_succ_add`)
read one bidegree at a time; that a coalgebra map is determined by its projection to letters
needs neither coassociativity nor conilpotence. For `C = Tᶜ(M)` itself the cofree lift is the
Taylor expansion `TauCeti.ReducedTensorWords.coalgHom`
(`LinearMap.IsConilpotent.cofreeLift_eq_coalgHom`).

Applied to the reduced bar construction `Tᶜ(sA)` of an algebra `A`, this identifies maps of
coalgebras from a conilpotent coalgebra `C` into the bar construction with linear maps `C ⟶ sA`;
the compatibility with differentials then singles out the twisting cochains, which is the bar side
of the bar–cobar adjunction.

## Main definitions

* `LinearMap.IsConilpotent.cofreeLift`: the coalgebra map `C ⟶ Tᶜ(N)` with prescribed projection
  `f : C ⟶ N` to letters.
* `LinearMap.IsConilpotent.coalgHomEquiv`: coalgebra maps `C ⟶ Tᶜ(N)` are in bijection with linear
  maps `C ⟶ N`.

## Main results

* `LinearMap.IsConilpotent.component_cofreeLift`: the length-`(n + 1)` component of the cofree
  lift is `f^{⊗(n + 1)} ∘ Δ⁽ⁿ⁾`.
* `LinearMap.IsConilpotent.letter_cofreeLift`, `LinearMap.IsConilpotent.letter_comp_cofreeLift`:
  its projection to letters is `f`.
* `LinearMap.IsConilpotent.deconcatenation_comp_cofreeLift`: for a coassociative coproduct, it is a
  coalgebra map.
* `LinearMap.IsConilpotent.eq_cofreeLift`: every coalgebra map into `Tᶜ(N)` is the cofree lift of
  its projection to letters.
* `LinearMap.IsConilpotent.cofreeLift_comp`, `LinearMap.IsConilpotent.map_comp_cofreeLift`:
  naturality in the coalgebra and in the cogenerators.

## References

* J.-L. Loday and B. Vallette, *Algebraic Operads*, Grundlehren der mathematischen Wissenschaften
  346, Springer (2012), Proposition 1.2.1 and Section 1.2.6, for the cofree property of the tensor
  coalgebra among conilpotent coalgebras.
* B. Keller, *Introduction to A-infinity algebras and modules*, Homology, Homotopy and
  Applications 3 (2001), Section 3.6.
-/

public section

open scoped TensorProduct

universe uR uC uD uN uP

namespace LinearMap.IsConilpotent

open TauCeti TauCeti.ReducedTensorWords

variable {R : Type uR} {C : Type uC} {D : Type uD} {N : Type uN} {P : Type uP} [CommSemiring R]
  [AddCommMonoid C] [Module R C] [AddCommMonoid D] [Module R D] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P] {Δ : C →ₗ[R] C ⊗[R] C}

/-- The summand of length `n + 1` of the cofree lift: `f^{⊗(n + 1)} ∘ Δ⁽ⁿ⁾`, included into reduced
tensor words. -/
private noncomputable def cofreeTerm (Δ : C →ₗ[R] C ⊗[R] C) (f : C →ₗ[R] N) (n : ℕ) :
    C →ₗ[R] ReducedTensorWords R N :=
  of R N ⟨n + 1, n.succ_pos⟩ ∘ₗ PiTensorProduct.map (fun _ ↦ f) ∘ₗ Δ.iteratedComul n

/-- Beyond the vanishing bound of the iterated coproducts of `c`, the summands vanish, so the
`finsum` defining the cofree lift is the finite sum below that bound. -/
private theorem finsum_cofreeTerm_eq (f : C →ₗ[R] N) {c : C} {n : ℕ}
    (hn : ∀ k, n ≤ k → Δ.iteratedComul k c = 0) :
    ∑ᶠ k, cofreeTerm Δ f k c = ∑ k ∈ Finset.range n, cofreeTerm Δ f k c := by
  refine finsum_eq_sum_of_support_subset _ fun k hk ↦ ?_
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra h
  exact hk (by simp only [cofreeTerm, LinearMap.comp_apply, hn k (not_lt.mp h), map_zero])

/-- The **cofree lift** of a linear map `f : C ⟶ N` along a conilpotent coproduct `Δ`: the map
`C ⟶ Tᶜ(N)` sending `c` to `∑_{n ≥ 0} f^{⊗(n + 1)} (Δ⁽ⁿ⁾ c)`, a finite sum by conilpotence. When
`Δ` is coassociative it is the unique coalgebra map with projection `f` to letters
(`LinearMap.IsConilpotent.coalgHomEquiv`).

Its body is sealed; reason about it through `LinearMap.IsConilpotent.cofreeLift_apply` and
`LinearMap.IsConilpotent.component_cofreeLift`. -/
noncomputable def cofreeLift (hΔ : Δ.IsConilpotent) (f : C →ₗ[R] N) :
    C →ₗ[R] ReducedTensorWords R N where
  toFun c := ∑ᶠ k, cofreeTerm Δ f k c
  map_add' c d := by
    obtain ⟨n₁, h₁⟩ := hΔ.exists_forall_iteratedComul_eq_zero c
    obtain ⟨n₂, h₂⟩ := hΔ.exists_forall_iteratedComul_eq_zero d
    obtain ⟨n₃, h₃⟩ := hΔ.exists_forall_iteratedComul_eq_zero (c + d)
    rw [finsum_cofreeTerm_eq f (n := max n₁ (max n₂ n₃)) fun k hk ↦ h₁ k (by omega),
      finsum_cofreeTerm_eq f (n := max n₁ (max n₂ n₃)) fun k hk ↦ h₂ k (by omega),
      finsum_cofreeTerm_eq f (n := max n₁ (max n₂ n₃)) fun k hk ↦ h₃ k (by omega)]
    simp only [map_add, Finset.sum_add_distrib]
  map_smul' r c := by
    obtain ⟨n₁, h₁⟩ := hΔ.exists_forall_iteratedComul_eq_zero c
    obtain ⟨n₂, h₂⟩ := hΔ.exists_forall_iteratedComul_eq_zero (r • c)
    rw [finsum_cofreeTerm_eq f (n := max n₁ n₂) fun k hk ↦ h₁ k (by omega),
      finsum_cofreeTerm_eq f (n := max n₁ n₂) fun k hk ↦ h₂ k (by omega)]
    simp only [map_smul, Finset.smul_sum, RingHom.id_apply]

variable (hΔ : Δ.IsConilpotent) (f : C →ₗ[R] N)

/-- The cofree lift on an element `c` is the finite sum of the terms `f^{⊗(k + 1)} (Δ⁽ᵏ⁾ c)`
below any bound beyond which the iterated coproducts of `c` vanish. -/
theorem cofreeLift_apply {c : C} {n : ℕ} (hn : ∀ k, n ≤ k → Δ.iteratedComul k c = 0) :
    hΔ.cofreeLift f c = ∑ k ∈ Finset.range n,
      of R N ⟨k + 1, k.succ_pos⟩ (PiTensorProduct.map (fun _ ↦ f) (Δ.iteratedComul k c)) :=
  finsum_cofreeTerm_eq f hn

/-- The length-`(n + 1)` component of the cofree lift is `f^{⊗(n + 1)} ∘ Δ⁽ⁿ⁾`. -/
@[simp]
theorem component_cofreeLift (n : ℕ) (c : C) :
    component R N ⟨n + 1, n.succ_pos⟩ (hΔ.cofreeLift f c) =
      PiTensorProduct.map (fun _ ↦ f) (Δ.iteratedComul n c) := by
  obtain ⟨m, hm⟩ := hΔ.exists_forall_iteratedComul_eq_zero c
  rw [hΔ.cofreeLift_apply f (n := max m (n + 1)) fun k hk ↦ hm k (by omega), map_sum,
    Finset.sum_eq_single_of_mem n (Finset.mem_range.mpr (by omega)), component_of]
  intro k _ hk
  exact component_of_of_ne R N (fun h ↦ hk (by simpa using h)) _

/-- The length-`(n + 1)` component of the cofree lift, as an equality of linear maps. -/
theorem component_comp_cofreeLift (n : ℕ) :
    component R N ⟨n + 1, n.succ_pos⟩ ∘ₗ hΔ.cofreeLift f =
      PiTensorProduct.map (fun _ ↦ f) ∘ₗ Δ.iteratedComul n :=
  LinearMap.ext (hΔ.component_cofreeLift f n)

/-- The length-one projection, presented through the index `⟨0 + 1, _⟩` that
`LinearMap.IsConilpotent.component_cofreeLift` produces for `n = 0`. The two indices agree by
definition, since the value of `(1 : {n : ℕ // 0 < n})` is `1` by definition (`Positive.val_one`);
rewriting along `Positive.val_one` itself is not possible, because the index determines the type
of the projection. -/
private theorem component_one_eq : component R N 1 = component R N ⟨0 + 1, Nat.succ_pos 0⟩ :=
  (rfl)

/-- The projection of the cofree lift of `f` onto single letters is `f`. -/
@[simp]
theorem letter_cofreeLift (c : C) : letter R N (hΔ.cofreeLift f c) = f c := by
  rw [letter_apply, component_one_eq, component_cofreeLift, LinearMap.iteratedComul_zero,
    TensorPower.oneEquiv_map, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

/-- The projection of the cofree lift of `f` onto single letters is `f`, as an equality of linear
maps. -/
@[simp]
theorem letter_comp_cofreeLift : letter R N ∘ₗ hΔ.cofreeLift f = f :=
  LinearMap.ext (hΔ.letter_cofreeLift f)

/-- **The cofree lift is a coalgebra map** when the coproduct is coassociative:
`Δ_{Tᶜ(N)} ∘ F = (F ⊗ F) ∘ Δ`. -/
theorem deconcatenation_comp_cofreeLift
    (hcoassoc : (TensorProduct.assoc R C C C).toLinearMap ∘ₗ Δ.rTensor C ∘ₗ Δ = Δ.lTensor C ∘ₗ Δ) :
    deconcatenation R N ∘ₗ hΔ.cofreeLift f =
      TensorProduct.map (hΔ.cofreeLift f) (hΔ.cofreeLift f) ∘ₗ Δ := by
  -- Compare the two sides in each bidegree `(i + 1, j + 1)`: cutting the length-`(i + j + 2)`
  -- component is splitting `Δ⁽ⁱ⁺ʲ⁺¹⁾`, which is `(Δ⁽ⁱ⁾ ⊗ Δ⁽ʲ⁾) ∘ Δ` by coassociativity.
  refine LinearMap.ext fun c ↦ tensor_ext_component R N fun ⟨p, hp⟩ ⟨q, hq⟩ ↦ ?_
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hp.ne'
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hq.ne'
  -- The component of length `(i + 1) + (j + 1)`, definitionally `(i + 1 + j) + 1`.
  have hc : component R N ⟨i + 1 + (j + 1), by omega⟩ (hΔ.cofreeLift f c) =
      PiTensorProduct.map (fun _ ↦ f) (Δ.iteratedComul (i + 1 + j) c) :=
    hΔ.component_cofreeLift f (i + 1 + j) c
  have hmul := LinearMap.congr_fun (TauCeti.TensorPower.mulEquiv_comp_map_const (R := R) (i + 1)
    (j + 1) f) (TensorProduct.map (Δ.iteratedComul i) (Δ.iteratedComul j) (Δ c))
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← LinearMap.comp_apply (TensorProduct.map _ _),
    map_component_comp_deconcatenation, TensorProduct.map_map, component_comp_cofreeLift,
    component_comp_cofreeLift, LinearMap.comp_apply]
  dsimp only
  rw [hc, LinearMap.iteratedComul_succ_add hcoassoc]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hmul ⊢
  rw [LinearEquiv.symm_apply_eq, ← TensorProduct.map_map]
  exact hmul.symm

/-- The length-`(n + 1)` component of a coalgebra map `F` into `Tᶜ(N)` is
`(π ∘ F)^{⊗(n + 1)} ∘ Δ⁽ⁿ⁾`, where `π` projects onto single letters. -/
private theorem component_comp_eq_of_deconcatenation_comp {F : C →ₗ[R] ReducedTensorWords R N}
    (hF : deconcatenation R N ∘ₗ F = TensorProduct.map F F ∘ₗ Δ) (n : ℕ) :
    component R N ⟨n + 1, n.succ_pos⟩ ∘ₗ F =
      PiTensorProduct.map (fun _ ↦ letter R N ∘ₗ F) ∘ₗ Δ.iteratedComul n := by
  have h1 : component R N 1 ∘ₗ F =
      (TauCeti.TensorPower.oneEquiv R N).symm.toLinearMap ∘ₗ letter R N ∘ₗ F := by
    refine LinearMap.ext fun c ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, letter_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  induction n with
  | zero =>
    rw [LinearMap.iteratedComul_zero, ← TauCeti.TensorPower.oneEquiv_symm_comp]
    exact h1
  | succ n ih =>
    -- Cut the component of length `n + 2` after its first `n + 1` letters.
    have hsplit : component R N ⟨n + 1 + 1, (n + 1).succ_pos⟩ =
        TensorPower.mulEquiv.toLinearMap ∘ₗ
          TensorProduct.map (component R N ⟨n + 1, n.succ_pos⟩) (component R N 1) ∘ₗ
            deconcatenation R N := by
      rw [component_one_eq, map_component_comp_deconcatenation, ← LinearMap.comp_assoc,
        LinearEquiv.comp_symm, LinearMap.id_comp]
    rw [hsplit, LinearMap.comp_assoc, LinearMap.comp_assoc, hF, ← LinearMap.comp_assoc _ _
      (TensorProduct.map _ _), ← TensorProduct.map_comp, ih, h1, LinearMap.iteratedComul_succ,
      TauCeti.TensorPower.oneEquiv_symm_comp, TensorProduct.map_comp]
    simp only [← LinearMap.comp_assoc]
    rw [TauCeti.TensorPower.mulEquiv_comp_map_const (n + 1) 1 (letter R N ∘ₗ F)]

/-- **A coalgebra map into `Tᶜ(N)` is the cofree lift of its projection to letters.** This uses
neither coassociativity nor conilpotence beyond the existence of the cofree lift. -/
theorem eq_cofreeLift {F : C →ₗ[R] ReducedTensorWords R N}
    (hF : deconcatenation R N ∘ₗ F = TensorProduct.map F F ∘ₗ Δ) :
    F = hΔ.cofreeLift (letter R N ∘ₗ F) :=
  linearMap_ext_component R N fun n ↦ by
    rw [component_comp_cofreeLift, component_comp_eq_of_deconcatenation_comp hF]

/-- **The cofree property of the reduced tensor coalgebra.** For a coassociative conilpotent
coproduct `Δ` on `C`, coalgebra maps `C ⟶ Tᶜ(N)` are in bijection with linear maps `C ⟶ N`, by
projecting onto single letters; the inverse is the cofree lift. -/
noncomputable def coalgHomEquiv
    (hcoassoc : (TensorProduct.assoc R C C C).toLinearMap ∘ₗ Δ.rTensor C ∘ₗ Δ = Δ.lTensor C ∘ₗ Δ) :
    {F : C →ₗ[R] ReducedTensorWords R N //
      deconcatenation R N ∘ₗ F = TensorProduct.map F F ∘ₗ Δ} ≃ (C →ₗ[R] N) where
  toFun F := letter R N ∘ₗ F.val
  invFun f := ⟨hΔ.cofreeLift f, hΔ.deconcatenation_comp_cofreeLift f hcoassoc⟩
  left_inv F := Subtype.ext (hΔ.eq_cofreeLift F.property).symm
  right_inv f := hΔ.letter_comp_cofreeLift f

@[simp]
theorem coalgHomEquiv_apply
    (hcoassoc : (TensorProduct.assoc R C C C).toLinearMap ∘ₗ Δ.rTensor C ∘ₗ Δ = Δ.lTensor C ∘ₗ Δ)
    (F : {F : C →ₗ[R] ReducedTensorWords R N //
      deconcatenation R N ∘ₗ F = TensorProduct.map F F ∘ₗ Δ}) :
    hΔ.coalgHomEquiv hcoassoc F = letter R N ∘ₗ F.val :=
  (rfl)

@[simp]
theorem coalgHomEquiv_symm_apply
    (hcoassoc : (TensorProduct.assoc R C C C).toLinearMap ∘ₗ Δ.rTensor C ∘ₗ Δ = Δ.lTensor C ∘ₗ Δ) :
    ((hΔ.coalgHomEquiv hcoassoc).symm f).val = hΔ.cofreeLift f :=
  (rfl)

/-- **Naturality in the coalgebra.** Precomposing a cofree lift with a coalgebra map `g : D ⟶ C`
gives the cofree lift of `f ∘ g`. -/
theorem cofreeLift_comp {Δ' : D →ₗ[R] D ⊗[R] D} (hΔ' : Δ'.IsConilpotent) {g : D →ₗ[R] C}
    (hg : Δ ∘ₗ g = TensorProduct.map g g ∘ₗ Δ') :
    hΔ.cofreeLift f ∘ₗ g = hΔ'.cofreeLift (f ∘ₗ g) :=
  linearMap_ext_component R N fun n ↦ by
    rw [← LinearMap.comp_assoc, component_comp_cofreeLift, component_comp_cofreeLift,
      LinearMap.comp_assoc, LinearMap.iteratedComul_comp hg, ← LinearMap.comp_assoc,
      ← PiTensorProduct.map_comp]

/-- **Naturality in the cogenerators.** Applying a linear map `g : N ⟶ P` to every letter of a
cofree lift gives the cofree lift of `g ∘ f`. -/
theorem map_comp_cofreeLift (g : N →ₗ[R] P) :
    ReducedTensorWords.map R g ∘ₗ hΔ.cofreeLift f = hΔ.cofreeLift (g ∘ₗ f) :=
  linearMap_ext_component R P fun n ↦ LinearMap.ext fun c ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, component_map,
      component_cofreeLift, component_cofreeLift, ← LinearMap.comp_apply (PiTensorProduct.map _),
      ← PiTensorProduct.map_comp]

/-- For the reduced tensor coalgebra `Tᶜ(M)` itself, the cofree lift of `f : Tᶜ(M) ⟶ N` is the
Taylor expansion `TauCeti.ReducedTensorWords.coalgHom`. -/
theorem cofreeLift_eq_coalgHom {M : Type*} [AddCommMonoid M] [Module R M]
    (f : ReducedTensorWords R M →ₗ[R] N) :
    (isConilpotent_deconcatenation R M).cofreeLift f = coalgHom R f := by
  rw [(isConilpotent_deconcatenation R M).eq_cofreeLift (isCoalgHom_iff.mp (isCoalgHom_coalgHom f)),
    letter_comp_coalgHom]

end LinearMap.IsConilpotent
