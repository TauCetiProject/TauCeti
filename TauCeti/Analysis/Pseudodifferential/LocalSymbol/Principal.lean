/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.LocalSymbol.Classical

/-!
# The principal symbol of a classical symbol on an open set

For an open set `U ⊆ ℝⁿ` of positions, the principal symbol of a classical symbol `a` of order `m`
on `U` (`TauCeti.LocalClassicalSymbol`) is its leading homogeneous term `a_m`, a homogeneous symbol
of degree `m` on `U`. This file proves that it fits into the exact sequence

`0 → S^{m-1}_cl(U) → S^m_cl(U) → H^m(U) → 0`

of complex vector spaces, as on `ℝⁿ` (`TauCeti.ClassicalSymbol.principalEquiv`), and that every
map in it commutes with restriction to smaller open sets, with the cut-off extension to `ℝⁿ` and
with the restriction of classical symbols on `ℝⁿ`. In a chart of a manifold this is the local
form of the principal symbol sequence of classical pseudodifferential operators; its compatibility
with restrictions is what lets the chartwise quotients be compared on overlaps.

* `TauCeti.LocalClassicalSymbol.principal`: the principal symbol, with
  `TauCeti.LocalClassicalSymbol.exists_sub_cutoffSymbol_principal`: the full symbol and its cut-off
  principal symbol differ by a symbol of order `m - 1` on `U`.
* `TauCeti.LocalClassicalSymbol.ofHomogeneous`: the classical symbol `χ(ξ) a(x, ξ)` of a single
  homogeneous term, whose principal symbol is `a`
  (`TauCeti.LocalClassicalSymbol.principal_surjective`).
* `TauCeti.LocalClassicalSymbol.inclusion`: a classical symbol of order `m - k`, `k ∈ ℕ`, is
  classical of order `m`, with `k` leading terms equal to zero.
* `TauCeti.LocalClassicalSymbol.tail`: the remainder `a - χ(ξ) a_m` after the principal term, a
  classical symbol of order `m - 1`.
* `TauCeti.LocalClassicalSymbol.principal_eq_zero_iff_exists_inclusion` and
  `TauCeti.LocalClassicalSymbol.ker_principalLinearMap`: the principal symbol vanishes exactly on
  the classical symbols of order `m - 1`; `TauCeti.LocalClassicalSymbol.principal_eq_zero_iff`:
  equivalently, exactly when the full symbol is a symbol of order `m - 1` on `U`.
* `TauCeti.LocalClassicalSymbol.principalEquiv`: the principal symbol identifies the quotient by
  the classical symbols of order `m - 1` with the homogeneous symbols of degree `m` on `U`.
* `TauCeti.LocalClassicalSymbol.principal_restrict`,
  `TauCeti.LocalClassicalSymbol.principal_extend` and
  `TauCeti.ClassicalSymbol.principal_restrict`, with the corresponding statements for
  `inclusion` and `ofHomogeneous`: the compatibility with restriction and cut-off extension.

## References

* R. Melrose, *Pseudodifferential operators on Euclidean space*, MIT 18.199 (2008), Chapter 2,
  §2.9, Lemma 2.5.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Definition 18.1.5.
-/

public section

noncomputable section

open scoped ContDiff
open Set Filter

namespace TauCeti

variable {n : ℕ}

namespace LocalClassicalSymbol

variable {U U' : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

/-! ### The principal symbol -/

section Principal

variable (a b : LocalClassicalSymbol U V W m)

/-- The principal symbol of a classical symbol of order `m` on `U`: its leading homogeneous term
`a_m`, of degree `m`. -/
def principal : LocalHomogeneousSymbol U V W m :=
  (a.term 0).castDegree (by simp)

theorem principal_def : a.principal = (a.term 0).castDegree (by simp) :=
  (rfl)

@[simp]
theorem coefficient_principal : a.principal.coefficient = (a.term 0).coefficient :=
  LocalHomogeneousSymbol.coefficient_castDegree _ _

/-- A classical symbol on `U` and its cut-off principal symbol differ by a symbol of order `m - 1`
on `U`. -/
theorem exists_sub_cutoffSymbol_principal (χ : FrequencyCutoff (CoordinateSpace n)) :
    ∃ r : LocalSymbol U V W (m - 1), r.coefficient =
      (a.toLocalSymbol - LocalHomogeneousSymbol.cutoffSymbol χ a.principal).coefficient :=
  ⟨LocalSymbol.inclusion (by simp) (a.remainder χ 1), funext fun p => by simp⟩

@[simp]
theorem principal_zero : (0 : LocalClassicalSymbol U V W m).principal = 0 :=
  LocalHomogeneousSymbol.castDegree_zero _

@[simp]
theorem principal_add : (a + b).principal = a.principal + b.principal :=
  LocalHomogeneousSymbol.castDegree_add _ _ _

@[simp]
theorem principal_smul (c : ℂ) : (c • a).principal = c • a.principal :=
  LocalHomogeneousSymbol.castDegree_smul _ _ _

@[simp]
theorem principal_neg : (-a).principal = -a.principal :=
  LocalHomogeneousSymbol.coefficient_injective (by simp)

@[simp]
theorem principal_sub : (a - b).principal = a.principal - b.principal :=
  LocalHomogeneousSymbol.coefficient_injective (by simp)

end Principal

/-! ### Single homogeneous terms -/

section OfHomogeneous

/-- The classical symbol `χ(ξ) a(x, ξ)` on `U` of a single homogeneous term `a` of degree `m` on
`U`: its principal symbol is `a` and its other homogeneous terms vanish. -/
def ofHomogeneous (χ : FrequencyCutoff (CoordinateSpace n)) (a : LocalHomogeneousSymbol U V W m) :
    LocalClassicalSymbol U V W m where
  toLocalSymbol := LocalHomogeneousSymbol.cutoffSymbol χ a
  term
    | 0 => a.castDegree (by simp)
    | _ + 1 => 0
  exists_remainder' := ⟨χ, fun
    | 0 => ⟨LocalSymbol.inclusion (by simp) (LocalHomogeneousSymbol.cutoffSymbol χ a),
        fun p => by simp⟩
    | N + 1 => ⟨0, fun p => by simp [Finset.sum_range_succ']⟩⟩

variable (χ : FrequencyCutoff (CoordinateSpace n)) (a : LocalHomogeneousSymbol U V W m)

@[simp]
theorem toLocalSymbol_ofHomogeneous :
    (ofHomogeneous χ a).toLocalSymbol = LocalHomogeneousSymbol.cutoffSymbol χ a :=
  (rfl)

@[simp]
theorem principal_ofHomogeneous : (ofHomogeneous χ a).principal = a :=
  LocalHomogeneousSymbol.castDegree_castDegree _ _ _ |>.trans
    (LocalHomogeneousSymbol.castDegree_rfl a)

@[simp]
theorem term_ofHomogeneous_succ (j : ℕ) : (ofHomogeneous χ a).term (j + 1) = 0 :=
  (rfl)

@[simp]
theorem ofHomogeneous_zero : ofHomogeneous χ (0 : LocalHomogeneousSymbol U V W m) = 0 :=
  ext (map_zero (LocalHomogeneousSymbol.cutoffSymbol χ))

/-- Every homogeneous symbol of degree `m` on `U` is the principal symbol of a classical symbol of
order `m` on `U`. -/
theorem principal_surjective :
    Function.Surjective (principal : LocalClassicalSymbol U V W m → _) :=
  fun a ↦ ⟨ofHomogeneous default a, principal_ofHomogeneous default a⟩

end OfHomogeneous

/-! ### Inclusion of orders -/

section Inclusion

variable {m' : ℝ}

/-- **Inclusion of orders.** A classical symbol of order `m' = m - k` on `U`, `k ∈ ℕ`, is a
classical symbol of order `m` on `U` whose first `k` homogeneous terms vanish, followed by the
terms of the original expansion. -/
def inclusion (k : ℕ) (hk : m' = m - k) :
    LocalClassicalSymbol U V W m' →ₗ[ℂ] LocalClassicalSymbol U V W m where
  toFun b :=
    { toLocalSymbol :=
        LocalSymbol.inclusion (hk.le.trans (sub_le_self m k.cast_nonneg)) b.toLocalSymbol
      term j := if h : k ≤ j then (b.term (j - k)).castDegree (by rw [hk, Nat.cast_sub h]; ring)
        else 0
      exists_remainder' := ⟨default, fun N => by
        rcases le_or_gt k N with hN | hN
        · -- After `N = k + M` terms the remainder is the remainder of `b` after `M` terms.
          obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
          refine ⟨LocalSymbol.inclusion (le_of_eq (by rw [hk]; push_cast; ring))
            (b.remainder default M), fun p => ?_⟩
          rw [LocalSymbol.coefficient_inclusion, coefficient_remainder,
            LocalSymbol.coefficient_inclusion, Finset.sum_range_add,
            Finset.sum_eq_zero (s := Finset.range k) fun j hj => ?_, zero_add]
          · congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [Nat.le_add_right, ↓reduceDIte,
              LocalHomogeneousSymbol.coefficient_castDegree]
            rw [LocalHomogeneousSymbol.coefficient_congr_index b.term
              (Nat.add_sub_cancel_left k i)]
          · simp [show ¬k ≤ j by simpa using hj]
        · -- Before the `k`-th term all terms vanish, and `b` has order `m - k ≤ m - N`.
          refine ⟨LocalSymbol.inclusion (by rw [hk]; gcongr) b.toLocalSymbol, fun p => ?_⟩
          rw [LocalSymbol.coefficient_inclusion, LocalSymbol.coefficient_inclusion,
            Finset.sum_eq_zero fun j hj => ?_, sub_zero]
          simp [show ¬k ≤ j by simp at hj; omega]⟩ }
  map_add' a b := ext (map_add (LocalSymbol.inclusion _) a.toLocalSymbol b.toLocalSymbol)
  map_smul' c a := ext (map_smul (LocalSymbol.inclusion _) c a.toLocalSymbol)

variable (k : ℕ) (hk : m' = m - k) (b : LocalClassicalSymbol U V W m')

@[simp]
theorem toLocalSymbol_inclusion :
    (inclusion k hk b).toLocalSymbol =
      LocalSymbol.inclusion (hk.le.trans (sub_le_self m k.cast_nonneg)) b.toLocalSymbol :=
  (rfl)

theorem term_inclusion (j : ℕ) :
    (inclusion k hk b).term j =
      if h : k ≤ j then (b.term (j - k)).castDegree (by rw [hk, Nat.cast_sub h]; ring) else 0 :=
  (rfl)

@[simp]
theorem term_inclusion_of_lt {j : ℕ} (hj : j < k) : (inclusion k hk b).term j = 0 := by
  simp [term_inclusion, show ¬k ≤ j by omega]

@[simp]
theorem term_inclusion_add (j : ℕ) :
    (inclusion k hk b).term (k + j) = (b.term j).castDegree (by rw [hk]; push_cast; ring) := by
  ext1
  simp only [term_inclusion, Nat.le_add_right, ↓reduceDIte,
    LocalHomogeneousSymbol.coefficient_castDegree]
  rw [LocalHomogeneousSymbol.coefficient_congr_index b.term (Nat.add_sub_cancel_left k j)]

/-- Including a classical symbol on `U` into an equal order (a change of the order's expression)
keeps its homogeneous terms. -/
@[simp]
theorem term_inclusion_zero (hk : m' = m - (0 : ℕ)) (j : ℕ) :
    (inclusion 0 hk b).term j = (b.term j).castDegree (by rw [hk]; simp) := by
  ext1
  simp only [term_inclusion, Nat.zero_le, ↓reduceDIte,
    LocalHomogeneousSymbol.coefficient_castDegree]
  rw [LocalHomogeneousSymbol.coefficient_congr_index b.term (Nat.sub_zero j)]

/-- Including a classical symbol on `U` into a strictly larger order kills its principal
symbol. -/
@[simp]
theorem principal_inclusion_succ (k : ℕ) (hk : m' = m - (k + 1 : ℕ)) :
    (inclusion (k + 1) hk b).principal = 0 := by
  ext1
  simp

theorem inclusion_injective :
    Function.Injective (inclusion (U := U) (V := V) (W := W) k hk) := fun _ _ h =>
  ext (LocalSymbol.inclusion_injective _ (congrArg toLocalSymbol h))

end Inclusion

/-! ### Removing the leading term -/

section Tail

variable (χ : FrequencyCutoff (CoordinateSpace n)) (a : LocalClassicalSymbol U V W m)

/-- **Removing the leading term.** The remainder `a - χ(ξ) a_m` of a classical symbol of order `m`
on `U` after its principal term, as a classical symbol of order `m - 1` on `U` with the
homogeneous terms `a_{m-1}, a_{m-2}, …`. -/
def tail : LocalClassicalSymbol U V W (m - 1) where
  toLocalSymbol := LocalSymbol.inclusion (le_of_eq (by simp)) (a.remainder χ 1)
  term j := (a.term (j + 1)).castDegree (by push_cast; ring)
  exists_remainder' := ⟨χ, fun N =>
    ⟨LocalSymbol.inclusion (le_of_eq (by push_cast; ring)) (a.remainder χ (N + 1)), fun p => by
      rw [LocalSymbol.coefficient_inclusion, LocalSymbol.coefficient_inclusion,
        coefficient_remainder, coefficient_remainder, Finset.sum_range_succ',
        Finset.sum_range_one]
      simp only [LocalHomogeneousSymbol.coefficient_castDegree]
      abel⟩⟩

@[simp]
theorem coefficient_toLocalSymbol_tail (p : CoordinateSpace n × CoordinateSpace n) :
    (a.tail χ).toLocalSymbol.coefficient p =
      a.toLocalSymbol.coefficient p - χ p.2 • (a.term 0).coefficient p := by
  simp [tail]

@[simp]
theorem term_tail (j : ℕ) :
    (a.tail χ).term j = (a.term (j + 1)).castDegree (by push_cast; ring) :=
  (rfl)

/-- A classical symbol on `U` is its cut-off principal term plus its tail, included back into
order `m`. -/
theorem inclusion_tail_add_ofHomogeneous :
    inclusion 1 (by simp) (a.tail χ) + ofHomogeneous χ a.principal = a :=
  ext <| LocalSymbol.ext <| funext fun p => by simp

end Tail

/-! ### The principal symbol sequence

The principal symbol fits into the exact sequence `0 → S^{m-1}_cl(U) → S^m_cl(U) → H^m(U) → 0`:
it is surjective onto the homogeneous symbols of degree `m` on `U`, and its kernel is the image of
the classical symbols of order `m - 1` on `U`. -/

section PrincipalSequence

variable (U V W m) in
/-- The principal symbol as a linear map. -/
def principalLinearMap : LocalClassicalSymbol U V W m →ₗ[ℂ] LocalHomogeneousSymbol U V W m where
  toFun := principal
  map_add' := principal_add
  map_smul' c a := principal_smul a c

@[simp]
theorem principalLinearMap_apply (a : LocalClassicalSymbol U V W m) :
    principalLinearMap U V W m a = a.principal :=
  (rfl)

/-- **The kernel of the principal symbol.** A classical symbol of order `m` on `U` has principal
symbol zero exactly when it is a classical symbol of order `m - 1` on `U`. -/
theorem principal_eq_zero_iff_exists_inclusion (a : LocalClassicalSymbol U V W m) :
    a.principal = 0 ↔ ∃ b : LocalClassicalSymbol U V W (m - 1), inclusion 1 (by simp) b = a := by
  refine ⟨fun h => ⟨a.tail default, ?_⟩, ?_⟩
  · -- With a vanishing leading term, `a` is the inclusion of its tail.
    simpa [h] using inclusion_tail_add_ofHomogeneous default a
  · rintro ⟨b, rfl⟩
    exact principal_inclusion_succ b 0 (by simp)

variable (U V W m) in
/-- **The kernel of the principal symbol** is the image of the classical symbols of order `m - 1`
on `U`. -/
theorem ker_principalLinearMap :
    LinearMap.ker (principalLinearMap U V W m) =
      LinearMap.range (inclusion (U := U) (V := V) (W := W) (m' := m - 1) 1 (by simp)) := by
  ext a
  simp only [LinearMap.mem_ker, principalLinearMap_apply, principal_eq_zero_iff_exists_inclusion,
    LinearMap.mem_range]

variable (U V W m) in
/-- The principal symbol identifies the quotient of the classical symbols of order `m` on `U` by
the classical symbols of order `m - 1` (`TauCeti.LocalClassicalSymbol.ker_principalLinearMap`)
with the homogeneous symbols of degree `m` on `U`. -/
def principalEquiv :
    (LocalClassicalSymbol U V W m ⧸
        LinearMap.range (inclusion (U := U) (V := V) (W := W) (m' := m - 1) 1 (by simp))) ≃ₗ[ℂ]
      LocalHomogeneousSymbol U V W m :=
  (Submodule.quotEquivOfEq _ _ (ker_principalLinearMap U V W m).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ principal_surjective)

@[simp]
theorem principalEquiv_mk (a : LocalClassicalSymbol U V W m) :
    principalEquiv U V W m (Submodule.Quotient.mk a) = a.principal :=
  (rfl)

end PrincipalSequence

/-! ### Restriction and cut-off extension -/

section Restrict

variable {U'' : TopologicalSpace.Opens (CoordinateSpace n)} {m' : ℝ}

/-- The principal symbol commutes with restriction to a smaller open set. -/
@[simp]
theorem principal_restrict (h : U' ≤ U) (a : LocalClassicalSymbol U V W m) :
    (restrict h a).principal = LocalHomogeneousSymbol.restrict h a.principal := by
  rw [principal_def, principal_def, term_restrict, LocalHomogeneousSymbol.restrict_castDegree]

/-- Inclusion of orders commutes with restriction to a smaller open set. -/
@[simp]
theorem restrict_inclusion (h : U' ≤ U) (k : ℕ) (hk : m' = m - k)
    (b : LocalClassicalSymbol U V W m') :
    restrict h (inclusion k hk b) = inclusion k hk (restrict h b) :=
  ext (by simp [LocalSymbol.restrict_inclusion])

/-- The classical symbol of a single homogeneous term commutes with restriction to a smaller open
set. -/
@[simp]
theorem restrict_ofHomogeneous (h : U' ≤ U) (χ : FrequencyCutoff (CoordinateSpace n))
    (a : LocalHomogeneousSymbol U V W m) :
    restrict h (ofHomogeneous χ a) = ofHomogeneous χ (LocalHomogeneousSymbol.restrict h a) :=
  ext (by simp)

end Restrict

section Extend

variable {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U) {m' : ℝ}

/-- The principal symbol commutes with the cut-off extension to `ℝⁿ`. -/
@[simp]
theorem principal_extend (a : LocalClassicalSymbol U V W m) :
    (extend ψ hψ hψU a).principal = LocalHomogeneousSymbol.extend ψ hψ hψU a.principal :=
  HomogeneousSymbol.ext (funext fun p => by simp)

/-- Inclusion of orders commutes with the cut-off extension to `ℝⁿ`. -/
@[simp]
theorem extend_inclusion (k : ℕ) (hk : m' = m - k) (b : LocalClassicalSymbol U V W m') :
    extend ψ hψ hψU (inclusion k hk b) = ClassicalSymbol.inclusion k hk (extend ψ hψ hψU b) :=
  ClassicalSymbol.ext (by simp [LocalSymbol.inclusion_extend])

/-- The classical symbol of a single homogeneous term commutes with the cut-off extension to
`ℝⁿ`. -/
@[simp]
theorem extend_ofHomogeneous (χ : FrequencyCutoff (CoordinateSpace n))
    (a : LocalHomogeneousSymbol U V W m) :
    extend ψ hψ hψU (ofHomogeneous χ a) =
      ClassicalSymbol.ofHomogeneous χ (LocalHomogeneousSymbol.extend ψ hψ hψU a) :=
  ClassicalSymbol.ext (by simp)

end Extend

/-- **The kernel of the principal symbol, by the full symbol.** A classical symbol of order `m` on
`U` has principal symbol zero exactly when its full symbol is a symbol of order `m - 1` on `U`. -/
theorem principal_eq_zero_iff {a : LocalClassicalSymbol U V W m} :
    a.principal = 0 ↔
      ∃ r : LocalSymbol U V W (m - 1), r.coefficient = a.toLocalSymbol.coefficient := by
  refine ⟨fun h => ?_, fun ⟨r, hr⟩ => ?_⟩
  · obtain ⟨r, hr⟩ := a.exists_sub_cutoffSymbol_principal default
    exact ⟨r, by simpa [h] using hr⟩
  · -- Each cut-off extension to `ℝⁿ` has full symbol of order `m - 1`, so its principal symbol
    -- vanishes by the statement on `ℝⁿ`.
    refine LocalHomogeneousSymbol.ext_of_extend fun ψ hψ hψU => ?_
    rw [map_zero, ← principal_extend hψ hψU a]
    exact ClassicalSymbol.principal_eq_zero_iff.2
      ⟨LocalSymbol.extend ψ hψ hψU r, funext fun p => by simp [hr]⟩

end LocalClassicalSymbol

namespace ClassicalSymbol

variable {U : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m m' : ℝ}

/-- The principal symbol of the restriction of a classical symbol on `ℝⁿ` to an open set is the
restriction of its principal symbol. -/
@[simp]
theorem principal_restrict (a : ClassicalSymbol n V W m) :
    (restrict U a).principal = HomogeneousSymbol.restrict U a.principal := by
  rw [LocalClassicalSymbol.principal_def, term_restrict, principal_def,
    HomogeneousSymbol.restrict_castDegree]

/-- Inclusion of orders commutes with the restriction of classical symbols on `ℝⁿ` to an open
set. -/
@[simp]
theorem restrict_inclusion (k : ℕ) (hk : m' = m - k) (b : ClassicalSymbol n V W m') :
    restrict U (inclusion k hk b) = LocalClassicalSymbol.inclusion k hk (restrict U b) :=
  LocalClassicalSymbol.ext (by simp [Symbol.restrict_inclusion])

/-- The classical symbol of a single homogeneous term commutes with the restriction of classical
symbols on `ℝⁿ` to an open set. -/
@[simp]
theorem restrict_ofHomogeneous (χ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    restrict U (ofHomogeneous χ a) =
      LocalClassicalSymbol.ofHomogeneous χ (HomogeneousSymbol.restrict U a) :=
  LocalClassicalSymbol.ext (by simp [HomogeneousSymbol.restrict_cutoffSymbol])

end ClassicalSymbol

end TauCeti
