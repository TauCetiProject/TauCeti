/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.HarishChandra
public import TauCeti.Algebra.Lie.Killing.CartanRestriction
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Symmetrization
-- Non-public: commutators lower the PBW degree, used only inside the proofs.
import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.AssociatedGraded

/-!
# The leading term of the Harish-Chandra projection

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field `K` of
characteristic zero, `H` a splitting Cartan subalgebra and `b` a base of its root system, so that
`L = n⁻ ⊕ H ⊕ n⁺`. This file shows that the Cartan projection
`TauCeti.cartanProjection b : U(L) → U(H)` is compatible with the PBW filtrations, and computes
its leading term.

* **Filtration.** If `u` has PBW degree at most `n`, so does its Cartan projection
  (`TauCeti.cartanProjection_mem_pbwFiltration`).
* **Leading term.** On a word `ι x₁ ⋯ ι xₙ` the Cartan projection is
  `ι (π x₁) ⋯ ι (π xₙ)` up to PBW degree strictly less than `n`, where
  `π = TauCeti.killingCartanProjection H` is the projection of `L` onto `H` along the root spaces
  (`TauCeti.cartanProjection_prod_map_ι_sub_mem_pbwFiltrationPrevious`).

Both rest on three rules for multiplying by a generator: a generator from `n⁻` on the left or one
from `n⁺` on the right is killed by the projection, and a generator `h` of `H` on the left passes
through it (`TauCeti.cartanProjection_ι_coe_mul`), because `ad h` preserves the
augmentation ideal of `U(n⁻)`. A generator `e` of `n⁺` on the left is moved to the right at the
cost of the commutator `⁅ι e, u⁆`, which has smaller PBW degree.

Read in `S(H)` through `U(H) ≃ S(H)`, the PBW filtration of `U(H)` is the degree filtration of
`S(H)`. On the centre this gives the two facts about the Harish-Chandra projection
`TauCeti.hcProjection b` that the degree induction proving the Harish-Chandra isomorphism needs:
it preserves degrees (`TauCeti.hcProjection_mem_wordFiltration`), and on the symmetrization of a
homogeneous Lie invariant `p` of degree `n` it agrees with the Chevalley restriction
`TauCeti.lieCartanRestriction H p` up to degree strictly less than `n`
(`TauCeti.hcProjection_sub_lieCartanRestriction_mem_wordFiltrationPrevious`).

## Main results

* `TauCeti.killingCartanProjection_eq_zero_of_mem_negativeNilradical` and
  `TauCeti.killingCartanProjection_eq_zero_of_mem_positiveNilradical`: the projection `π` of `L`
  onto `H` vanishes on both nilradicals.
* `TauCeti.cartanProjection_ι_mul_of_mem_negativeNilradical`,
  `TauCeti.cartanProjection_mul_ι_of_mem_positiveNilradical` and
  `TauCeti.cartanProjection_ι_coe_mul`: the three multiplication rules.
* `TauCeti.cartanProjection_mem_pbwFiltration`: the Cartan projection preserves PBW degree.
* `TauCeti.cartanProjection_prod_map_ι_sub_mem_pbwFiltrationPrevious`: its leading term on words.
* `TauCeti.cartanProjection_pbwHomogeneousSymmetrization_sub_mem_pbwFiltrationPrevious`: its
  leading term on symmetrizations is the Chevalley restriction.
* `TauCeti.hcProjection_mem_wordFiltration` and
  `TauCeti.hcProjection_sub_lieCartanRestriction_mem_wordFiltrationPrevious`: the same for the
  Harish-Chandra projection, in `S(H)`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.3.
-/

public section

namespace TauCeti

open LieAlgebra

universe u v

section Filtration

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

local notation "U" => _root_.UniversalEnvelopingAlgebra K

/-! ### The projection onto `H` on the nilradicals -/

/-- The Killing-orthogonal projection onto `H` vanishes on the span of any set of root spaces. -/
theorem killingCartanProjection_eq_zero_of_mem_rootSpaceSpan {S : Set H.root} {x : L}
    (hx : x ∈ rootSpaceSpan H S) : killingCartanProjection H x = 0 := by
  have hle : (rootSpaceSpan H S : Submodule K L) ≤ LinearMap.ker (killingCartanProjection H) := by
    rw [rootSpaceSpan_eq_iSup, LieSubmodule.iSup_toSubmodule]
    exact iSup_le fun α _ hy ↦ killingCartanProjection_eq_zero_of_mem_rootSpace
      (Finset.mem_filter.mp (α : H.root).2).2 hy
  exact hle hx

variable (b : (IsKilling.rootSystem H).Base)

/-- The Killing-orthogonal projection onto `H` vanishes on the negative nilradical. -/
theorem killingCartanProjection_eq_zero_of_mem_negativeNilradical {x : L}
    (hx : x ∈ negativeNilradical H b) : killingCartanProjection H x = 0 :=
  killingCartanProjection_eq_zero_of_mem_rootSpaceSpan ((mem_negativeNilradical H b x).mp hx)

/-- The Killing-orthogonal projection onto `H` vanishes on the positive nilradical. -/
theorem killingCartanProjection_eq_zero_of_mem_positiveNilradical {x : L}
    (hx : x ∈ positiveNilradical H b) : killingCartanProjection H x = 0 :=
  killingCartanProjection_eq_zero_of_mem_rootSpaceSpan ((mem_positiveNilradical H b x).mp hx)

/-! ### Multiplying by a generator -/

/-- **A generator from `n⁻` on the left is killed by the Cartan projection**: the augmentation of
`U(n⁻)` vanishes on its generators. -/
theorem cartanProjection_ι_mul_of_mem_negativeNilradical {x : L}
    (hx : x ∈ negativeNilradical H b) (u : U L) :
    cartanProjection b (_root_.UniversalEnvelopingAlgebra.ι K x * u) = 0 := by
  have hι : _root_.UniversalEnvelopingAlgebra.ι K x =
      UniversalEnvelopingAlgebra.map K (negativeNilradical H b).incl
        (_root_.UniversalEnvelopingAlgebra.ι K (⟨x, hx⟩ : negativeNilradical H b)) := by
    rw [UniversalEnvelopingAlgebra.map_ι, LieSubalgebra.coe_incl]
  have key : cartanProjection b ∘ₗ LinearMap.mulLeft K (_root_.UniversalEnvelopingAlgebra.ι K x) =
      0 := by
    refine UniversalEnvelopingAlgebra.linearMap_ext_triangular b fun f h e ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.zero_apply, ← mul_assoc,
      ← mul_assoc, hι, ← map_mul, cartanProjection_mul_mul, ← Bialgebra.counitAlgHom_apply,
      map_mul, Bialgebra.counitAlgHom_apply, UniversalEnvelopingAlgebra.counit_ι, zero_mul,
      zero_mul, zero_smul]
  simpa using LinearMap.congr_fun key u

/-- **A generator from `n⁺` on the right is killed by the Cartan projection**: the augmentation of
`U(n⁺)` vanishes on its generators. -/
theorem cartanProjection_mul_ι_of_mem_positiveNilradical {x : L}
    (hx : x ∈ positiveNilradical H b) (u : U L) :
    cartanProjection b (u * _root_.UniversalEnvelopingAlgebra.ι K x) = 0 := by
  have hι : _root_.UniversalEnvelopingAlgebra.ι K x =
      UniversalEnvelopingAlgebra.map K (positiveNilradical H b).incl
        (_root_.UniversalEnvelopingAlgebra.ι K (⟨x, hx⟩ : positiveNilradical H b)) := by
    rw [UniversalEnvelopingAlgebra.map_ι, LieSubalgebra.coe_incl]
  have key : cartanProjection b ∘ₗ LinearMap.mulRight K (_root_.UniversalEnvelopingAlgebra.ι K x) =
      0 := by
    refine UniversalEnvelopingAlgebra.linearMap_ext_triangular b fun f h e ↦ ?_
    have hε : Coalgebra.counit (R := K)
        (e * _root_.UniversalEnvelopingAlgebra.ι K (⟨x, hx⟩ : positiveNilradical H b)) = 0 := by
      rw [← Bialgebra.counitAlgHom_apply, map_mul, Bialgebra.counitAlgHom_apply,
        Bialgebra.counitAlgHom_apply, UniversalEnvelopingAlgebra.counit_ι, mul_zero]
    rw [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.zero_apply, mul_assoc, hι,
      ← map_mul, cartanProjection_mul_mul, hε, mul_zero, zero_smul]
  simpa using LinearMap.congr_fun key u

/-- Bracketing with a generator `h` of `H` preserves the augmentation ideal of `U(n⁻)`: moving `ι h`
past an element `f` of `U(n⁻)` costs an element of `U(n⁻)` with augmentation zero. -/
private theorem exists_counit_eq_zero_ι_mul_eq (h : H) (f : U (negativeNilradical H b)) :
    ∃ g : U (negativeNilradical H b), Coalgebra.counit (R := K) g = 0 ∧
      _root_.UniversalEnvelopingAlgebra.ι K (h : L) *
          UniversalEnvelopingAlgebra.map K (negativeNilradical H b).incl f =
        UniversalEnvelopingAlgebra.map K (negativeNilradical H b).incl f *
            _root_.UniversalEnvelopingAlgebra.ι K (h : L) +
          UniversalEnvelopingAlgebra.map K (negativeNilradical H b).incl g := by
  induction f using UniversalEnvelopingAlgebra.induction_ι with
  | ι y =>
    -- the negative nilradical is a sum of root spaces, so it is stable under `ad h`
    have hy : ⁅(h : L), (y : L)⁆ ∈ negativeNilradical H b :=
      (mem_negativeNilradical H b _).mpr <| LieSubmodule.lie_mem _ (x := h)
        ((mem_negativeNilradical H b _).mp y.2)
    refine ⟨_root_.UniversalEnvelopingAlgebra.ι K (⟨_, hy⟩ : negativeNilradical H b),
      UniversalEnvelopingAlgebra.counit_ι K _ _, ?_⟩
    rw [UniversalEnvelopingAlgebra.map_ι, UniversalEnvelopingAlgebra.map_ι]
    simp only [LieSubalgebra.coe_incl, LieHom.map_lie, Ring.lie_def]
    abel
  | algebraMap r => exact ⟨0, map_zero _, by simp [Algebra.commutes]⟩
  | add f f' hf hf' =>
    obtain ⟨g, hg, hfg⟩ := hf
    obtain ⟨g', hg', hfg'⟩ := hf'
    refine ⟨g + g', by rw [map_add, hg, hg', add_zero], ?_⟩
    rw [map_add, mul_add, hfg, hfg', map_add, add_mul]
    abel
  | mul f f' hf hf' =>
    obtain ⟨g, hg, hfg⟩ := hf
    obtain ⟨g', hg', hfg'⟩ := hf'
    refine ⟨g * f' + f * g', ?_, ?_⟩
    · simp only [← Bialgebra.counitAlgHom_apply, map_add, map_mul] at hg hg' ⊢
      rw [hg, hg', zero_mul, mul_zero, add_zero]
    · rw [map_mul, ← mul_assoc, hfg, add_mul, mul_assoc, hfg', map_add, map_mul, map_mul]
      noncomm_ring

/-- **A generator from `H` on the left passes through the Cartan projection**:
`cartanProjection b (ι h * u) = ι h * cartanProjection b u` for `h` in `H`. -/
theorem cartanProjection_ι_coe_mul (h : H) (u : U L) :
    cartanProjection b (_root_.UniversalEnvelopingAlgebra.ι K (h : L) * u) =
      _root_.UniversalEnvelopingAlgebra.ι K h * cartanProjection b u := by
  have hι : _root_.UniversalEnvelopingAlgebra.ι K (h : L) =
      UniversalEnvelopingAlgebra.map K H.incl (_root_.UniversalEnvelopingAlgebra.ι K h) := by
    rw [UniversalEnvelopingAlgebra.map_ι, LieSubalgebra.coe_incl]
  have key : cartanProjection b ∘ₗ
        LinearMap.mulLeft K (_root_.UniversalEnvelopingAlgebra.ι K (h : L)) =
      LinearMap.mulLeft K (_root_.UniversalEnvelopingAlgebra.ι K h) ∘ₗ cartanProjection b := by
    refine UniversalEnvelopingAlgebra.linearMap_ext_triangular b fun f k e ↦ ?_
    obtain ⟨g, hg, hfg⟩ := exists_counit_eq_zero_ι_mul_eq b h f
    rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, ← mul_assoc, ← mul_assoc, hfg, add_mul, add_mul, map_add,
      mul_assoc (UniversalEnvelopingAlgebra.map K _ f), hι, ← map_mul, cartanProjection_mul_mul,
      cartanProjection_mul_mul, cartanProjection_mul_mul, hg, zero_mul, zero_smul, add_zero,
      mul_smul_comm]
  simpa using LinearMap.congr_fun key u

/-- The Cartan projection of `ι x * w`: writing `x = f + h + e` along `L = n⁻ ⊕ H ⊕ n⁺`, the
generator `f` contributes nothing, `h = π x` passes through, and `e` contributes the projection of
the commutator `ι e * w - w * ι e`. -/
private theorem exists_cartanProjection_ι_mul_eq (x : L) (w : U L) :
    ∃ e ∈ positiveNilradical H b,
      cartanProjection b (_root_.UniversalEnvelopingAlgebra.ι K x * w) =
        _root_.UniversalEnvelopingAlgebra.ι K (killingCartanProjection H x) *
            cartanProjection b w +
          cartanProjection b (_root_.UniversalEnvelopingAlgebra.ι K e * w -
            w * _root_.UniversalEnvelopingAlgebra.ι K e) := by
  obtain ⟨f, hf, y, hy, rfl⟩ := exists_mem_negativeNilradical_add_mem_borelSubalgebra H b x
  rw [← LieSubalgebra.mem_toSubmodule, borelSubalgebra_toSubmodule, Submodule.mem_sup] at hy
  obtain ⟨h, hh, e, he, rfl⟩ := hy
  refine ⟨e, he, ?_⟩
  have hπ : killingCartanProjection H (f + (h + e)) = ⟨h, hh⟩ := by
    rw [map_add, map_add, killingCartanProjection_eq_zero_of_mem_negativeNilradical b hf,
      killingCartanProjection_eq_zero_of_mem_positiveNilradical b he, zero_add, add_zero]
    exact killingCartanProjection_coe H ⟨h, hh⟩
  rw [hπ, map_add, map_add, add_mul, add_mul, map_add, map_add,
    cartanProjection_ι_mul_of_mem_negativeNilradical b hf, zero_add,
    cartanProjection_ι_coe_mul b ⟨h, hh⟩, map_sub,
    cartanProjection_mul_ι_of_mem_positiveNilradical b he, sub_zero]

/-! ### The PBW filtration -/

/-- **The Cartan projection preserves PBW degree**: if `u` is a combination of words of at most
`n` generators in `U(L)`, then `cartanProjection b u` is one in `U(H)`. -/
theorem cartanProjection_mem_pbwFiltration {n : ℕ} {u : U L}
    (hu : u ∈ UniversalEnvelopingAlgebra.pbwFiltration K L n) :
    cartanProjection b u ∈ UniversalEnvelopingAlgebra.pbwFiltration K H n := by
  induction n generalizing u with
  | zero =>
    rw [UniversalEnvelopingAlgebra.pbwFiltration_zero] at hu
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hu
    rw [cartanProjection_algebraMap]
    exact UniversalEnvelopingAlgebra.algebraMap_mem_pbwFiltration K H r 0
  | succ n ih =>
    refine (UniversalEnvelopingAlgebra.pbwFiltration_le_iff K L
      (p := (UniversalEnvelopingAlgebra.pbwFiltration K H (n + 1)).comap
        (cartanProjection b))).2 (fun l hl ↦ ?_) hu
    rcases l with _ | ⟨x, l⟩
    · simpa using UniversalEnvelopingAlgebra.one_mem_pbwFiltration K H (n + 1)
    · have hw := UniversalEnvelopingAlgebra.prod_map_ι_mem_pbwFiltration K L
        (k := n) (l := l) (by simpa using hl)
      obtain ⟨e, he, heq⟩ := exists_cartanProjection_ι_mul_eq b x (l.map _).prod
      rw [Submodule.mem_comap, List.map_cons, List.prod_cons, heq]
      refine add_mem ?_ (UniversalEnvelopingAlgebra.pbwFiltration_mono K H n.le_succ (ih ?_))
      · simpa [add_comm] using UniversalEnvelopingAlgebra.mul_mem_pbwFiltration K H
          (UniversalEnvelopingAlgebra.ι_mem_pbwFiltration_one K H _) (ih hw)
      · simpa [add_comm] using UniversalEnvelopingAlgebra.mul_sub_mul_mem_pbwFiltrationPrevious K L
          (UniversalEnvelopingAlgebra.ι_mem_pbwFiltration_one K L e) hw

/-- **The Cartan projection preserves a strict PBW degree bound**: the companion of
`TauCeti.cartanProjection_mem_pbwFiltration` for the step preceding degree `n`. -/
theorem cartanProjection_mem_pbwFiltrationPrevious {n : ℕ} {u : U L}
    (hu : u ∈ UniversalEnvelopingAlgebra.pbwFiltrationPrevious K L n) :
    cartanProjection b u ∈ UniversalEnvelopingAlgebra.pbwFiltrationPrevious K H n := by
  cases n with
  | zero =>
    rw [UniversalEnvelopingAlgebra.pbwFiltrationPrevious_zero, Submodule.mem_bot] at hu
    simp [hu]
  | succ n =>
    rw [UniversalEnvelopingAlgebra.pbwFiltrationPrevious_succ] at hu ⊢
    exact cartanProjection_mem_pbwFiltration b hu

/-- **The leading term of the Cartan projection on a word**: the Cartan projection of
`ι x₁ ⋯ ι xₙ` is `ι (π x₁) ⋯ ι (π xₙ)` up to PBW degree strictly less than `n`, where `π` is the
Killing-orthogonal projection `TauCeti.killingCartanProjection H` of `L` onto `H`. -/
theorem cartanProjection_prod_map_ι_sub_mem_pbwFiltrationPrevious (l : List L) :
    cartanProjection b (l.map (_root_.UniversalEnvelopingAlgebra.ι K)).prod -
        (l.map fun x ↦ _root_.UniversalEnvelopingAlgebra.ι K (killingCartanProjection H x)).prod ∈
      UniversalEnvelopingAlgebra.pbwFiltrationPrevious K H l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    obtain ⟨e, he, heq⟩ := exists_cartanProjection_ι_mul_eq b x (l.map _).prod
    have hw := UniversalEnvelopingAlgebra.prod_map_ι_mem_pbwFiltration K L (l := l) le_rfl
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [heq, add_sub_right_comm, ← mul_sub]
    refine add_mem ?_ ?_
    · simpa [add_comm] using UniversalEnvelopingAlgebra.mul_mem_pbwFiltrationPrevious_right K H
        (UniversalEnvelopingAlgebra.ι_mem_pbwFiltration_one K H _) ih
    · rw [UniversalEnvelopingAlgebra.pbwFiltrationPrevious_succ]
      refine cartanProjection_mem_pbwFiltration b ?_
      simpa [add_comm] using UniversalEnvelopingAlgebra.mul_sub_mul_mem_pbwFiltrationPrevious K L
        (UniversalEnvelopingAlgebra.ι_mem_pbwFiltration_one K L e) hw

/-- **The Harish-Chandra projection preserves degree**: a central element of PBW degree at most
`n` has Harish-Chandra projection of degree at most `n` in `S(H)`. -/
theorem hcProjection_mem_wordFiltration {n : ℕ} {z : Subalgebra.center K (U L)}
    (hz : (z : U L) ∈ UniversalEnvelopingAlgebra.pbwFiltration K L n) :
    hcProjection b z ∈ Algebra.wordFiltration (SymmetricAlgebra.ι K H) n := by
  rw [hcProjection_apply,
    UniversalEnvelopingAlgebra.symmetricAlgebraEquiv_symm_mem_wordFiltration_iff]
  exact cartanProjection_mem_pbwFiltration b hz

end Filtration

/-! ### Symmetrizations -/

section Symmetrization

variable {K : Type} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]
  (b : (IsKilling.rootSystem H).Base)

local notation "U" => _root_.UniversalEnvelopingAlgebra K

/-- **The leading term of the Cartan projection on a symmetrization is the Chevalley
restriction**: for `p` homogeneous of degree `n` in `S(L)`, the Cartan projection of its PBW
symmetrization agrees with the restriction `TauCeti.lieCartanRestriction H p`, read in
`U(H) = S(H)`, up to PBW degree strictly less than `n`. -/
theorem cartanProjection_pbwHomogeneousSymmetrization_sub_mem_pbwFiltrationPrevious {n : ℕ}
    (hn : IsUnit (n.factorial : K)) (p : SymmetricAlgebra.homogeneousSubmodule K L n) :
    cartanProjection b (UniversalEnvelopingAlgebra.pbwHomogeneousSymmetrization K L n hn p) -
        UniversalEnvelopingAlgebra.symmetricAlgebraEquiv K H (lieCartanRestriction H p) ∈
      UniversalEnvelopingAlgebra.pbwFiltrationPrevious K H n := by
  obtain ⟨t, rfl⟩ := (SymmetricPower.equivHomogeneous (R := K) (M := L) n).surjective p
  rw [UniversalEnvelopingAlgebra.pbwHomogeneousSymmetrization_equivHomogeneous,
    SymmetricPower.coe_equivHomogeneous_apply]
  refine LinearMap.apply_mem_of_forall_symmetricPower_tprod
    (cartanProjection b ∘ₗ UniversalEnvelopingAlgebra.pbwSymmetrization K L n hn -
      (UniversalEnvelopingAlgebra.symmetricAlgebraEquiv K H).toLinearMap ∘ₗ
        (lieCartanRestriction H).toLinearMap ∘ₗ SymmetricPower.toSymmetricAlgebra K L n)
    _ (fun m ↦ ?_) t
  -- the restriction of the product of the `m i` is the product of the generators `π (m i)`
  have hres : UniversalEnvelopingAlgebra.symmetricAlgebraEquiv K H
      (lieCartanRestriction H (SymmetricPower.toSymmetricAlgebra K L n (⨂ₛ[K] i, m i))) =
        (List.ofFn fun i ↦
          _root_.UniversalEnvelopingAlgebra.ι K (killingCartanProjection H (m i))).prod := by
    simp [List.prod_ofFn]
  have hsym : cartanProjection b (UniversalEnvelopingAlgebra.pbwSymmetrization K L n hn
        (⨂ₛ[K] i, m i)) -
      cartanProjection b (List.ofFn fun i ↦ _root_.UniversalEnvelopingAlgebra.ι K (m i)).prod ∈
        UniversalEnvelopingAlgebra.pbwFiltrationPrevious K H n := by
    rw [← map_sub]
    exact cartanProjection_mem_pbwFiltrationPrevious b
      (UniversalEnvelopingAlgebra.pbwSymmetrization_tprod_sub_mem_pbwFiltrationPrevious K L n hn m)
  have hword := cartanProjection_prod_map_ι_sub_mem_pbwFiltrationPrevious b (List.ofFn m)
  rw [List.map_ofFn, List.map_ofFn, List.length_ofFn] at hword
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, AlgEquiv.toLinearMap_apply, hres]
  simpa only [sub_add_sub_cancel, Function.comp_def] using add_mem hsym hword

/-- **The leading term of the Harish-Chandra projection is the Chevalley restriction**: if the
central element `z` is the PBW symmetrization of `p`, homogeneous of degree `n` (such a `p` is a
Lie invariant, by `TauCeti.UniversalEnvelopingAlgebra.pbwHomogeneousSymmetrization_mem_center_iff`),
then `hcProjection b z` agrees with the restriction `TauCeti.lieCartanRestriction H p` up to degree
strictly less than `n` in `S(H)`. -/
theorem hcProjection_sub_lieCartanRestriction_mem_wordFiltrationPrevious {n : ℕ}
    (hn : IsUnit (n.factorial : K)) (p : SymmetricAlgebra.homogeneousSubmodule K L n)
    {z : Subalgebra.center K (U L)}
    (hz : (z : U L) = UniversalEnvelopingAlgebra.pbwHomogeneousSymmetrization K L n hn p) :
    hcProjection b z - lieCartanRestriction H p ∈
      Algebra.wordFiltrationPrevious (SymmetricAlgebra.ι K H) n := by
  rw [hcProjection_apply, hz, ← AlgEquiv.symm_apply_apply
      (UniversalEnvelopingAlgebra.symmetricAlgebraEquiv K H) (lieCartanRestriction H p),
    ← map_sub, UniversalEnvelopingAlgebra.symmetricAlgebraEquiv_symm_mem_wordFiltrationPrevious_iff]
  exact cartanProjection_pbwHomogeneousSymmetrization_sub_mem_pbwFiltrationPrevious b hn p

end Symmetrization

end TauCeti
