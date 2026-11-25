/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import TauCeti.GroupTheory.PGroup.FixedPointSum
public import TauCeti.RepresentationTheory.GroupAlgebra.RelativeTrace
import TauCeti.GroupTheory.Subgroup.Centralizer

/-!
# The Brauer homomorphism

For a subgroup `P` of `G`, the **Brauer projection** `Br_P : R[G] → R[C_G(P)]` keeps the
coefficients of an element of `R[G]` on the centralizer `C_G(P)` and discards the others
(`TauCeti.brauerProjection`). It is `R`-linear on all of `R[G]` and is not multiplicative there:
in `S₃` with `P = ⟨(12)⟩` and `r` a `3`-cycle, `Br_P(r · r²) = 1` while `Br_P(r) = Br_P(r²) = 0`.
It vanishes exactly on the elements with no coefficient on `C_G(P)`, and conjugation by `g`
carries its kernel at `P` to its kernel at `gPg⁻¹`. Since `x` has finite support, `Br_Q(x) ≠ 0`
for every `Q` in a nonempty directed family of subgroups implies the same at their supremum.

When `P` is a `p`-group and `R` has characteristic `p`, `Br_P` is multiplicative on the fixed
points `R[G]^P` of conjugation by `P` (`TauCeti.brauerProjection_mul`), and so restricts to an
algebra homomorphism `R[G]^P → R[C_G(P)]`, the **Brauer homomorphism** (`TauCeti.brauerHom`).
Both hypotheses are needed: over `ℚ`, `x = r + r²` gives
`Br_P(x²) = 2` but `Br_P(x)² = 0`; and over `𝔽₂` with `P = C₃` and `x` the sum of the
transpositions, `Br_P(x²) = 1 + r + r²` but `Br_P(x)² = 0`.

For `Q ≤ P`, `C_G(P) ≤ C_G(Q)` and `Br_P` factors through `Br_Q`
(`TauCeti.brauerProjection_eq_comapDomain`).

The Brauer projection of an element of `R[G]` invariant under conjugation by `N_G(P)` is again
invariant under `N_G(P)`, which acts on `C_G(P)`
(`TauCeti.coeff_brauerProjection_conj_of_mem_conjInvariants`). In particular the image of
`Z(R[G])` lies in `R[C_G(P)]^{N_G(P)}`.

For a `p`-group `P` in characteristic `p`, the kernel of `brauerHom` is the sum of the relative
trace ideals `R[G]^P_Q` (`TauCeti.relTraceIdeal`) over `Q < P`: see
`TauCeti.brauerProjection_relTrace_eq_zero` and `TauCeti.ker_brauerHom` in
`TauCeti.RepresentationTheory.GroupAlgebra.Brauer.Kernel`. The defect groups of the blocks of
`R[G]` are the maximal `p`-subgroups `P` on which the Brauer homomorphism of the block idempotent
is nonzero; this is not formalized here.

## Main definitions

* `TauCeti.brauerProjection P`: the coefficient projection `R[G] → R[C_G(P)]`.
* `TauCeti.brauerHom hP`: the Brauer homomorphism `R[G]^P →ₐ[R] R[C_G(P)]` for a `p`-group `P`
  in characteristic `p`.

## Main results

* `TauCeti.brauerProjection_eq_zero_iff`: `Br_P(x) = 0` exactly when `x` vanishes on `C_G(P)`.
* `TauCeti.brauerProjection_sSup_ne_zero_of_directedOn`: if `Br_Q(x) ≠ 0` for every `Q` in a
  nonempty directed family `c`, then `Br_{sSup c}(x) ≠ 0`.
* `TauCeti.brauerProjection_conj_eq_zero_iff`: `Br_{gPg⁻¹}(g x g⁻¹) = 0 ↔ Br_P(x) = 0`.
* `TauCeti.brauerProjection_conj_eq_zero_iff_of_conjRepresentation_eq`: if `g x g⁻¹ = x`, for
  instance if `x` is central, then `Br_{gPg⁻¹}(x) = 0 ↔ Br_P(x) = 0`.
* `TauCeti.brauerProjection_mul`: `Br_P(x y) = Br_P(x) Br_P(y)` for `x, y ∈ R[G]^P`.
* `TauCeti.coeff_brauerProjection_conj_of_mem_conjInvariants`: `Br_P` of an element invariant
  under conjugation by `N_G(P)`, for instance a central one, is invariant under `N_G(P)`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, §12.5, p. 243, and
  Corollary 12.5.4, p. 246.
* A. Martínez, *Modular representation theory of finite groups*, Theorem 4.1, p. 23.
-/

public section

namespace TauCeti

open MonoidAlgebra
open scoped Pointwise

variable {R G : Type*} [CommSemiring R] [Group G]

/-- The **Brauer projection** `Br_P : R[G] → R[C_G(P)]`, which keeps the coefficients on the
centralizer of `P` and discards the others. It is linear on all of `R[G]`, and multiplicative on
`R[G]^P` when `P` is a `p`-group in characteristic `p` (`TauCeti.brauerProjection_mul`). -/
noncomputable def brauerProjection (P : Subgroup G) :
    MonoidAlgebra R G →ₗ[R] MonoidAlgebra R (Subgroup.centralizer (P : Set G)) where
  toFun := comapDomain Subtype.val Subtype.val_injective
  map_add' := comapDomain_add _ _
  map_smul' c x := by
    ext
    simp

/-- The coefficient of `Br_P(x)` at `c ∈ C_G(P)` is the coefficient of `x` at `c`. -/
@[simp]
theorem coeff_brauerProjection (P : Subgroup G) (x : MonoidAlgebra R G)
    (c : Subgroup.centralizer (P : Set G)) :
    (brauerProjection P x).coeff c = x.coeff c := by
  simp [brauerProjection]

/-- `Br_P(x) = 0` exactly when `x` has no nonzero coefficient on the centralizer `C_G(P)`. -/
theorem brauerProjection_eq_zero_iff {P : Subgroup G} {x : MonoidAlgebra R G} :
    brauerProjection P x = 0 ↔ ∀ c ∈ Subgroup.centralizer (P : Set G), x.coeff c = 0 := by
  constructor
  · intro h c hc
    simpa using congrArg (fun y => y.coeff ⟨c, hc⟩) h
  · intro h
    ext c
    simpa using h c c.property

/-- `Br_1(x) = 0` exactly when `x = 0`, since the trivial subgroup is centralized by all of `G`. -/
theorem brauerProjection_bot_eq_zero_iff {x : MonoidAlgebra R G} :
    brauerProjection (⊥ : Subgroup G) x = 0 ↔ x = 0 := by
  rw [brauerProjection_eq_zero_iff]
  refine ⟨fun h => ?_, fun h c _ => by simp [h]⟩
  ext c
  simpa using h c (by simp [Subgroup.mem_centralizer_iff])

/-- **The Brauer projection at a directed supremum.** If `Br_Q(x) ≠ 0` for every member `Q` of a
nonempty directed family `c` of subgroups, for instance of a chain, then `Br_{sSup c}(x) ≠ 0`. -/
theorem brauerProjection_sSup_ne_zero_of_directedOn {c : Set (Subgroup G)} (hne : c.Nonempty)
    (hc : DirectedOn (· ≤ ·) c) {x : MonoidAlgebra R G}
    (h : ∀ Q ∈ c, brauerProjection Q x ≠ 0) : brauerProjection (sSup c) x ≠ 0 := by
  -- The member `S` of `c` whose centralizer meets the finite support of `x` in the fewest points
  -- gives a point of the support centralizing every member of `c`.
  classical
  let F : Subgroup G → Finset G :=
    fun S => x.coeff.support.filter (· ∈ Subgroup.centralizer (S : Set G))
  have hF : ∀ {S T : Subgroup G}, S ≤ T → F T ⊆ F S := fun hST y hy => by
    simp only [F, Finset.mem_filter] at hy ⊢
    exact ⟨hy.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hST) hy.2⟩
  obtain ⟨S, hS, hmin⟩ := exists_minimalFor_of_wellFoundedLT (· ∈ c) (fun S => (F S).card) hne
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ Subgroup.centralizer (S : Set G), x.coeff y ≠ 0 := by
    by_contra! hy
    exact h S hS (brauerProjection_eq_zero_iff.2 hy)
  have hyS : y ∈ F S := Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 hyx, hy⟩
  -- `y` centralizes every member of `c`.
  have hall : ∀ T ∈ c, y ∈ Subgroup.centralizer (T : Set G) := fun T hT => by
    obtain ⟨U, hU, hSU, hTU⟩ := hc S hS T hT
    rw [← Finset.eq_of_subset_of_card_le (hF hSU) (hmin hU (Finset.card_le_card (hF hSU)))]
      at hyS
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hTU) (Finset.mem_filter.1 hyS).2
  rw [Ne, brauerProjection_eq_zero_iff]
  push Not
  refine ⟨y, Subgroup.mem_centralizer_iff.2 fun g hg => ?_, hyx⟩
  obtain ⟨T, hT, hgT⟩ := (Subgroup.mem_sSup_of_directedOn hne hc).1 hg
  exact Subgroup.mem_centralizer_iff.1 (hall T hT) g hgT

/-- **Conjugation and the Brauer projection.** `Br_{gPg⁻¹}(g x g⁻¹) = 0` exactly when
`Br_P(x) = 0`. -/
theorem brauerProjection_conj_eq_zero_iff (g : G) {P : Subgroup G} {x : MonoidAlgebra R G} :
    brauerProjection (MulAut.conj g • P) (conjRepresentation R G g x) = 0 ↔
      brauerProjection P x = 0 := by
  rw [brauerProjection_eq_zero_iff, brauerProjection_eq_zero_iff, Subgroup.coe_pointwise_smul,
    Subgroup.centralizer_pointwise_smul]
  constructor
  · intro h c hc
    simpa [mul_assoc] using h _ (Subgroup.smul_mem_pointwise_smul c (MulAut.conj g) _ hc)
  · intro h c hc
    rw [coeff_conjRepresentation]
    refine h _ ((Subgroup.smul_mem_pointwise_smul_iff (a := MulAut.conj g)).1 ?_)
    simpa [mul_assoc] using hc

/-- **The Brauer projection of a conjugation-fixed element.** If conjugation by `g` fixes `x`, for
instance if `x` is central, then `Br_{gPg⁻¹}(x) = 0` exactly when `Br_P(x) = 0`. -/
theorem brauerProjection_conj_eq_zero_iff_of_conjRepresentation_eq {g : G} {P : Subgroup G}
    {x : MonoidAlgebra R G} (hx : conjRepresentation R G g x = x) :
    brauerProjection (MulAut.conj g • P) x = 0 ↔ brauerProjection P x = 0 := by
  rw [← brauerProjection_conj_eq_zero_iff g (P := P) (x := x), hx]

/-- `Br_P` keeps a basis element `single c r` with `c ∈ C_G(P)`. -/
@[simp]
theorem brauerProjection_single_coe (P : Subgroup G) (c : Subgroup.centralizer (P : Set G))
    (r : R) : brauerProjection P (single (c : G) r) = single c r :=
  comapDomain_single_map Subtype.val Subtype.val_injective c r

/-- `Br_P` keeps a basis element `single g r` with `g ∈ C_G(P)`. -/
theorem brauerProjection_single_of_mem (P : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.centralizer (P : Set G)) (r : R) :
    brauerProjection P (single g r) = single ⟨g, hg⟩ r :=
  brauerProjection_single_coe P ⟨g, hg⟩ r

/-- `Br_P` discards a basis element `single g r` with `g ∉ C_G(P)`. -/
theorem brauerProjection_single_of_notMem (P : Subgroup G) {g : G}
    (hg : g ∉ Subgroup.centralizer (P : Set G)) (r : R) :
    brauerProjection P (single g r) = 0 :=
  comapDomain_single_of_notMem_range (by simpa using hg) Subtype.val_injective

/-- `Br_P(1) = 1`, since `1 ∈ C_G(P)`. -/
@[simp]
theorem brauerProjection_one (P : Subgroup G) :
    brauerProjection P (1 : MonoidAlgebra R G) = 1 := by
  rw [one_def, one_def, ← brauerProjection_single_coe, OneMemClass.coe_one]

/-- **The Brauer projection factors through smaller subgroups.** For `Q ≤ P`, `Br_P` is `Br_Q`
followed by restriction of coefficients from `C_G(Q)` to `C_G(P) ≤ C_G(Q)`. -/
theorem brauerProjection_eq_comapDomain {Q P : Subgroup G} (hQP : Q ≤ P) (x : MonoidAlgebra R G) :
    brauerProjection P x =
      comapDomain (Subgroup.inclusion (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hQP)))
        (Subgroup.inclusion_injective _) (brauerProjection Q x) := by
  ext c
  simp

/-- **The Brauer projection is invariant under the normalizer.** If `z` is fixed by conjugation
by `H` and `n ∈ H` normalizes `P`, then `Br_P(z)` is fixed by conjugation by `n`, which acts on
`C_G(P)`. For `H = G`, so `z` is central (`TauCeti.center_le_conjInvariants`), the image of
`Z(R[G])` lies in `R[C_G(P)]^{N_G(P)}`. -/
theorem coeff_brauerProjection_conj_of_mem_conjInvariants {P H : Subgroup G}
    {z : MonoidAlgebra R G} (hz : z ∈ conjInvariants R H) {n : G} (hnH : n ∈ H)
    (hn : n ∈ Subgroup.normalizer (P : Set G)) (c : Subgroup.centralizer (P : Set G)) :
    (brauerProjection P z).coeff
        ⟨n * c * n⁻¹, (Subgroup.normal_subgroupOf_iff (Subgroup.centralizer_le_normalizer _)).1
          inferInstance (c : G) n c.property hn⟩ =
      (brauerProjection P z).coeff c := by
  rw [coeff_brauerProjection, coeff_brauerProjection]
  exact mem_conjInvariants_iff_coeff.1 hz n hnH c

/-- **The Brauer map is multiplicative.** For a `p`-subgroup `P` of a finite group `G` and `R` of
characteristic `p`, the Brauer projection is multiplicative on the elements of `R[G]` fixed by
conjugation by `P` (Webb, §12.5, p. 243, and Corollary 12.5.4, p. 246). -/
theorem brauerProjection_mul [Finite G] {p : ℕ} [Fact p.Prime] [CharP R p] {P : Subgroup G}
    (hP : IsPGroup p P) {x y : MonoidAlgebra R G} (hx : x ∈ conjInvariants R P)
    (hy : y ∈ conjInvariants R P) :
    brauerProjection P (x * y) = brauerProjection P x * brauerProjection P y := by
  classical
  have := Fintype.ofFinite G
  let : MulAction P G := MulAction.compHom G (MulAut.conj.comp P.subtype)
  have hsmul (g : P) (a : G) : g • a = g * a * (g : G)⁻¹ := by
    rw [MulAction.compHom_smul_def]
    simp
  ext c
  have hc := Subgroup.mem_centralizer_iff.1 c.property
  rw [coeff_brauerProjection, coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp),
    coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp)]
  simp only [coeff_brauerProjection]
  rw [IsPGroup.sum_eq_sum_fixedPoints hP (fun a : G => x.coeff a * y.coeff (a⁻¹ * c)) ?_]
  · refine Finset.sum_subtype _ (fun a => ?_) (fun a : G => x.coeff a * y.coeff (a⁻¹ * c)) |>.trans
      (Fintype.sum_congr _ _ fun a => by simp)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, MulAction.mem_fixedPoints, hsmul,
      Subgroup.mem_centralizer_iff, SetLike.mem_coe]
    refine ⟨fun h m hm => ?_, fun h m => ?_⟩
    · simpa [mul_inv_eq_iff_eq_mul] using h ⟨m, hm⟩
    · rw [h m m.property, mul_inv_cancel_right]
  · intro g a
    have hgc : (g : G)⁻¹ * c = c * (g : G)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hc g g.property, mul_inv_cancel_right]
    rw [hsmul, (mem_conjInvariants_iff_coeff.1 hx) g g.property a]
    congr 1
    rw [← (mem_conjInvariants_iff_coeff.1 hy) g g.property (a⁻¹ * c)]
    congr 1
    simp only [mul_inv_rev, inv_inv, mul_assoc, hgc]

/-- The **Brauer homomorphism** `R[G]^P → R[C_G(P)]` of a `p`-subgroup `P` of a finite group `G`
in characteristic `p`: the restriction of the Brauer projection to the fixed points of
conjugation by `P`, multiplicative by `TauCeti.brauerProjection_mul`. -/
noncomputable def brauerHom [Finite G] {p : ℕ} [Fact p.Prime] [CharP R p] {P : Subgroup G}
    (hP : IsPGroup p P) :
    conjInvariants R P →ₐ[R] MonoidAlgebra R (Subgroup.centralizer (P : Set G)) :=
  AlgHom.ofLinearMap (brauerProjection P ∘ₗ (conjInvariants R P).val.toLinearMap)
    (by simp) fun x y => by simpa using brauerProjection_mul hP x.property y.property

/-- The Brauer homomorphism is the Brauer projection on `R[G]^P`. -/
@[simp]
theorem brauerHom_apply [Finite G] {p : ℕ} [Fact p.Prime] [CharP R p] {P : Subgroup G}
    (hP : IsPGroup p P) (x : conjInvariants R P) :
    brauerHom hP x = brauerProjection P (x : MonoidAlgebra R G) := by
  simp [brauerHom]

end TauCeti
