/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.TateCohomology.HerbrandQuotient
public import TauCeti.RepresentationTheory.Homological.TateCohomology.HomologySequence
public import TauCeti.RepresentationTheory.Homological.TateCohomology.TrivialityCriterion
public import TauCeti.RepresentationTheory.Pi
import TauCeti.SetTheory.Cardinal.Finite

/-!
# Tate cohomology of a product of representations

Let `G` be a finite group and `M i` a family of representations of `G`, indexed by an arbitrary
type `ι`. This file shows that Tate cohomology commutes with the product `Rep.pi M` in every
integer degree:

`H-hat^n(G, ∏ i, M i) ≃ ∏ i, H-hat^n(G, M i)`,

the `i`-th component being induced by the projection onto `M i` (`linearEquivPi`).

Degrees `0` and `-1` rest on the low-degree descriptions `H-hat^0 = Mᴳ / N_G M` and
`H-hat^(-1) = ker N_G / I_G M`, where invariants, norms and the augmentation submodule `I_G M` of a
product are all computed componentwise. For the norm image and the augmentation submodule this
needs a choice in every factor at once, and for the latter also the finiteness of `G`
(`Representation.mem_coinvariantsKer_pi_iff`). By Tate's triviality criterion, which needs only
two consecutive degrees on the subgroups of prime-power order, a product of cohomologically
trivial representations is then cohomologically trivial (`isZero_res_pi`). The
products of the dimension-shifting sequences `0 → M i → Coind_⊥^G (M i) → ⋯ → 0` and
`0 → ⋯ → Ind_⊥^G (M i) → M i → 0` are short exact with cohomologically trivial middle terms, so
their connecting maps, which are natural in the projections, carry the low-degree computation to
every degree.

Consequently the **Herbrand quotient of a product** is the product of the Herbrand quotients of
the factors, as soon as all but finitely many factors have trivial Tate cohomology in degrees `0`
and `-1`. This is the shape of the `S`-ideles of a Galois extension `L/K` of number fields: they
are the product over the places `v` of `K` of the Galois modules `∏_{w ∣ v} L_wˣ` for `v ∈ S` and
`∏_{w ∣ v} 𝒪_wˣ` for `v ∉ S`, and the factors of the second kind are cohomologically trivial
when `L/K` is unramified at `v`.

## Main definitions

* `TauCeti.TateCohomology.linearEquivPi`: `H-hat^n(G, ∏ i, M i) ≃ ∏ i, H-hat^n(G, M i)` for every
  `n : ℤ`.

## Main results

* `TauCeti.TateCohomology.linearEquivPi_zero_H0π` and
  `TauCeti.TateCohomology.linearEquivPi_negOne_HNegOneπ`: in degrees `0` and `-1` the equivalence
  sends the class of an element to the family of the classes of its components.
* `TauCeti.TateCohomology.isZero_res_pi`: a product of cohomologically trivial
  representations is cohomologically trivial.
* `TauCeti.TateCohomology.herbrandQuotient_pi`: `h(∏ i, M i) = ∏ i ∈ s, h(M i)` when the factors
  outside the finite set `s` have trivial Tate cohomology in degrees `0` and `-1`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §2.
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII, §§6–7.
-/

public noncomputable section

universe u

open CategoryTheory Limits LinearMap Rep

namespace TauCeti.TateCohomology

variable {R G ι : Type u} [CommRing R] [Group G] [Fintype G] (M : ι → Rep R G)

omit [Fintype G] in
/-- The projection of a product onto a factor, as a compatible pair along the identity of `G`. -/
private theorem isIntertwiningMap_proj (i : ι) :
    (Rep.pi M).ρ.IsIntertwiningMap ((M i).ρ.comp ((MulEquiv.refl G : G ≃* G) : G →* G))
      (LinearMap.proj i) :=
  ⟨fun _ _ ↦ by simp⟩

/-! ### Degree zero -/

/-- The family of the maps `H-hat^0(G, ∏ j, M j) → H-hat^0(G, M i)` induced by the projections. -/
private def H0ToPi : tateCohomology (Rep.pi M) 0 →ₗ[R] ∀ i, tateCohomology (M i) 0 :=
  LinearMap.pi fun i ↦ (map (isIntertwiningMap_proj M i) 0).hom

private theorem H0ToPi_H0π (y : (Rep.pi M).ρ.invariants) (i : ι) :
    H0ToPi M (H0π (Rep.pi M) y) i =
      H0π (M i) ⟨y.1 i, ((Representation.mem_invariants_pi_iff _).1 y.2) i⟩ := by
  simp only [H0ToPi, LinearMap.pi_apply]
  exact (H0π_comp_map_apply (isIntertwiningMap_proj M i) y).trans
    (congrArg _ (Subtype.ext (mapInvariants_apply_coe _ y)))

private theorem H0ToPi_bijective : Function.Bijective (H0ToPi M) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using H0_induction_on with | h y => ?_
    -- Every component of `y` is a norm; a choice of preimages in all factors at once is a
    -- preimage of `y`.
    have h (i : ι) : ∃ z : M i, (M i).ρ.norm z = y.1 i := by
      obtain ⟨z, hz⟩ := (H0π_eq_zero_iff _).1 ((H0ToPi_H0π M y i).symm.trans (congrFun hx i))
      exact ⟨z, hz⟩
    choose z hz using h
    exact (H0π_eq_zero_iff y).2 ⟨z, funext fun i ↦ by simpa using hz i⟩
  · intro x
    have h (i : ι) : ∃ y : (M i).ρ.invariants, H0π (M i) y = x i :=
      H0_induction_on (C := fun x ↦ ∃ y, H0π (M i) y = x) (x i) fun y ↦ ⟨y, rfl⟩
    choose y hy using h
    refine ⟨H0π (Rep.pi M) ⟨fun i ↦ (y i).1, (Representation.mem_invariants_pi_iff _).2
      fun i ↦ (y i).2⟩, funext fun i ↦ ?_⟩
    rw [H0ToPi_H0π, ← hy i]

/-! ### Degree minus one -/

/-- The family of the maps `H-hat^(-1)(G, ∏ j, M j) → H-hat^(-1)(G, M i)` induced by the
projections. -/
private def HNegOneToPi : tateCohomology (Rep.pi M) (-1) →ₗ[R] ∀ i, tateCohomology (M i) (-1) :=
  LinearMap.pi fun i ↦ (map (isIntertwiningMap_proj M i) (-1)).hom

private theorem HNegOneToPi_HNegOneπ (y : ker (Rep.pi M).ρ.norm) (i : ι) :
    HNegOneToPi M (HNegOneπ (Rep.pi M) y) i =
      HNegOneπ (M i) ⟨y.1 i, (Representation.mem_ker_norm_pi_iff _).1 y.2 i⟩ := by
  simp only [HNegOneToPi, LinearMap.pi_apply]
  exact (HNegOneπ_comp_map_apply (isIntertwiningMap_proj M i) y).trans
    (congrArg _ (Subtype.ext (mapKerNorm_apply_coe _ y)))

private theorem HNegOneToPi_bijective : Function.Bijective (HNegOneToPi M) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using HNegOne_induction_on with | h y => ?_
    rw [HNegOneπ_eq_zero_iff, Submodule.submoduleOf, Submodule.mem_comap,
      Submodule.subtype_apply, Representation.mem_coinvariantsKer_pi_iff]
    intro i
    have := (HNegOneπ_eq_zero_iff _).1 ((HNegOneToPi_HNegOneπ M y i).symm.trans (congrFun hx i))
    rwa [Submodule.submoduleOf, Submodule.mem_comap] at this
  · intro x
    have h (i : ι) : ∃ y : ker (M i).ρ.norm, HNegOneπ (M i) y = x i :=
      HNegOne_induction_on (C := fun x ↦ ∃ y, HNegOneπ (M i) y = x) (x i) fun y ↦ ⟨y, rfl⟩
    choose y hy using h
    refine ⟨HNegOneπ (Rep.pi M) ⟨fun i ↦ (y i).1,
      (Representation.mem_ker_norm_pi_iff _).2 fun i ↦ (y i).2⟩, funext fun i ↦ ?_⟩
    rw [HNegOneToPi_HNegOneπ, ← hy i]

/-! ### Products of cohomologically trivial representations -/

omit [Fintype G] in
/-- **A product of cohomologically trivial representations is cohomologically trivial.** By Tate's
triviality criterion it suffices to check degrees `-1` and `0` on the subgroups of prime-power
order, where the Tate cohomology of the product is the product of the Tate cohomologies. -/
theorem isZero_res_pi [Finite G]
    (hM : ∀ i (S : Subgroup G) [Fintype S] (n : ℤ),
      IsZero (tateCohomology (Rep.res S.subtype (M i)) n))
    (S : Subgroup G) [Fintype S] (n : ℤ) :
    IsZero (tateCohomology (Rep.res S.subtype (Rep.pi M)) n) := by
  refine isZero_of_forall_isPGroup (Rep.pi M) (q := -1) (fun p _ P _ _ ↦ ?_)
    (fun p _ P _ _ ↦ ?_) S n
  -- Restricting the product to `P` gives the product of the restrictions.
  · refine IsZero.of_iso ?_ ((tateCohomologyFunctor (-1)).mapIso (Rep.resPiIso M P.subtype))
    have (i : ι) := ModuleCat.subsingleton_of_isZero (hM i P (-1))
    have :=
      (Equiv.ofBijective _ (HNegOneToPi_bijective fun i ↦ Rep.res P.subtype (M i))).subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  · rw [neg_add_cancel]
    refine IsZero.of_iso ?_ ((tateCohomologyFunctor 0).mapIso (Rep.resPiIso M P.subtype))
    have (i : ι) := ModuleCat.subsingleton_of_isZero (hM i P 0)
    have := (Equiv.ofBijective _ (H0ToPi_bijective fun i ↦ Rep.res P.subtype (M i))).subsingleton
    exact ModuleCat.isZero_of_subsingleton _

/-- A product of cohomologically trivial representations has vanishing Tate cohomology. -/
theorem isZero_pi
    (hM : ∀ i (S : Subgroup G) [Fintype S] (n : ℤ),
      IsZero (tateCohomology (Rep.res S.subtype (M i)) n))
    (n : ℤ) : IsZero (tateCohomology (Rep.pi M) n) :=
  isZero_of_forall_isZero_res _ (isZero_res_pi M hM) n

/-! ### Every degree -/

/-- The family of the maps `H-hat^n(G, ∏ j, M j) → H-hat^n(G, M i)` induced by the projections. -/
private def toPi (n : ℤ) : tateCohomology (Rep.pi M) n →ₗ[R] ∀ i, tateCohomology (M i) n :=
  LinearMap.pi fun i ↦ ((tateCohomologyFunctor n).map (Rep.piProj M i)).hom

private theorem map_isIntertwiningMap_proj (n : ℤ) (i : ι) :
    map (isIntertwiningMap_proj M i) n = (tateCohomologyFunctor n).map (Rep.piProj M i) := by
  rw [map_refl]
  congr 1
  ext x
  exact (Rep.piProj_hom_apply i x).symm

private theorem toPi_zero : toPi M 0 = H0ToPi M := by
  ext x i
  simp only [toPi, H0ToPi, LinearMap.pi_apply, map_isIntertwiningMap_proj]

private theorem toPi_negOne : toPi M (-1) = HNegOneToPi M := by
  ext x i
  simp only [toPi, HNegOneToPi, LinearMap.pi_apply, map_isIntertwiningMap_proj]

/-- The connecting maps of a product of short exact sequences with cohomologically trivial middle
terms transport bijectivity of `toPi` from the third to the first terms, one degree up. -/
private theorem toPi_bijective_of_shortExact {A B C : ι → Rep R G} (f : ∀ i, A i ⟶ B i)
    (g : ∀ i, B i ⟶ C i) (hfg : ∀ i, f i ≫ g i = 0)
    (hS : ∀ i, (ShortComplex.mk (f i) (g i) (hfg i)).ShortExact)
    (hB : ∀ i (S : Subgroup G) [Fintype S] (n : ℤ),
      IsZero (tateCohomology (Rep.res S.subtype (B i)) n))
    (n : ℤ) :
    Function.Bijective (toPi C n) ↔ Function.Bijective (toPi A (n + 1)) := by
  have hP := Rep.shortExact_pi (fun i ↦ ShortComplex.mk (f i) (g i) (hfg i)) hS
  have hB' (i : ι) := isZero_of_forall_isZero_res _ (hB i)
  -- the connecting map of the product, and the product of the connecting maps
  have hδ := δ_bijective_of_isZero_X₂ hP n (isZero_pi _ hB n)
    (isZero_pi _ hB (n + 1))
  let e (i : ι) :=
    Equiv.ofBijective _ (δ_bijective_of_isZero_X₂ (hS i) n (hB' i n) (hB' i (n + 1)))
  have hcomm : toPi A (n + 1) ∘ (_root_.TateCohomology.δ hP n).hom =
      Equiv.piCongrRight e ∘ toPi C n := by
    funext x
    funext i
    exact congr($(_root_.TateCohomology.δ_naturality hP (hS i)
      { τ₁ := Rep.piProj A i, τ₂ := Rep.piProj B i, τ₃ := Rep.piProj C i
        comm₁₂ := (Rep.piMap_piProj f i).symm, comm₂₃ := (Rep.piMap_piProj g i).symm } n).hom x)
  rw [← Function.Bijective.of_comp_iff' (Equiv.piCongrRight e).bijective, ← hcomm,
    Function.Bijective.of_comp_iff _ hδ]

/-- `toPi` is bijective in every degree, for every family: degree `0` is the low-degree
computation, and the dimension-shifting sequences move bijectivity up and down one degree. -/
private theorem toPi_bijective (n : ℤ) : ∀ M : ι → Rep R G, Function.Bijective (toPi M n) := by
  induction n using Int.induction_on with
  | zero => exact fun M ↦ toPi_zero M ▸ H0ToPi_bijective M
  | succ n ih =>
    intro M
    exact (toPi_bijective_of_shortExact (fun i ↦ coindBotUnit (M i))
      (fun i ↦ dimensionShiftUpπ (M i)) (fun i ↦ coindBotUnit_comp_dimensionShiftUpπ (M i))
      (fun i ↦ by simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_shortExact (M i))
      (fun i S _ m ↦ isZero_res_coindBot S (M i).V m) n).1 (ih _)
  | pred n ih =>
    intro M
    refine (toPi_bijective_of_shortExact (fun i ↦ dimensionShiftDownι (M i))
      (fun i ↦ indBotCounit (M i)) (fun i ↦ dimensionShiftDownι_comp_indBotCounit (M i))
      (fun i ↦ by
        simpa only [dimensionShiftDownSES_def] using dimensionShiftDownSES_shortExact (M i))
      (fun i S _ m ↦ isZero_res_indBot S (M i).V m) _).2 ?_
    rw [sub_add_cancel]
    exact ih _

/-- **Tate cohomology commutes with products** in every integer degree:
`H-hat^n(G, ∏ i, M i) ≃ ∏ i, H-hat^n(G, M i)`, the `i`-th component being induced by the
projection onto `M i`. -/
def linearEquivPi (n : ℤ) : tateCohomology (Rep.pi M) n ≃ₗ[R] ∀ i, tateCohomology (M i) n :=
  LinearEquiv.ofBijective (toPi M n) (toPi_bijective n M)

/-- The `i`-th component of `linearEquivPi` is induced by the projection onto `M i`. -/
@[simp]
theorem linearEquivPi_apply (n : ℤ) (x : tateCohomology (Rep.pi M) n) (i : ι) :
    linearEquivPi M n x i = ((tateCohomologyFunctor n).map (Rep.piProj M i)).hom x :=
  (rfl)

/-- In degree `0`, `linearEquivPi` sends the class of an invariant element of the product to the
family of the classes of its components. -/
theorem linearEquivPi_zero_H0π (y : (Rep.pi M).ρ.invariants) (i : ι) :
    linearEquivPi M 0 (H0π (Rep.pi M) y) i =
      H0π (M i) ⟨y.1 i, ((Representation.mem_invariants_pi_iff _).1 y.2) i⟩ := by
  rw [← H0ToPi_H0π, ← toPi_zero]
  rfl

/-- In degree `-1`, `linearEquivPi` sends the class of a norm-zero element of the product to the
family of the classes of its components. -/
theorem linearEquivPi_negOne_HNegOneπ (y : ker (Rep.pi M).ρ.norm) (i : ι) :
    linearEquivPi M (-1) (HNegOneπ (Rep.pi M) y) i =
      HNegOneπ (M i) ⟨y.1 i, (Representation.mem_ker_norm_pi_iff _).1 y.2 i⟩ := by
  rw [← HNegOneToPi_HNegOneπ, ← toPi_negOne]
  rfl

/-! ### The Herbrand quotient of a product -/

/-- **The Herbrand quotient of a product** of representations of a finite group is the product of
the Herbrand quotients of the factors, when the factors outside a finite set `s` have trivial Tate
cohomology in degrees `0` and `-1`. In particular, for a finite index type it is the product of
all the Herbrand quotients. -/
theorem herbrandQuotient_pi (s : Finset ι)
    (h0 : ∀ i ∉ s, Subsingleton (tateCohomology (M i) 0))
    (h1 : ∀ i ∉ s, Subsingleton (tateCohomology (M i) (-1))) :
    herbrandQuotient (Rep.pi M) = ∏ i ∈ s, herbrandQuotient (M i) := by
  simp only [herbrandQuotient_def]
  rw [Nat.card_congr (linearEquivPi M 0).toEquiv, Nat.card_congr (linearEquivPi M (-1)).toEquiv,
    Nat.card_pi_eq_prod_of_card_eq_one s fun i hi ↦ have := h0 i hi; Nat.card_of_subsingleton 0,
    Nat.card_pi_eq_prod_of_card_eq_one s fun i hi ↦ have := h1 i hi; Nat.card_of_subsingleton 0,
    Nat.cast_prod, Nat.cast_prod, Finset.prod_div_distrib]

end TauCeti.TateCohomology
