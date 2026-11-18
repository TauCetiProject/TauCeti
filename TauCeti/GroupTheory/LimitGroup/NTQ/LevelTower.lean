/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.NTQ.Tower
public import TauCeti.GroupTheory.CSA
import TauCeti.GroupTheory.FreeGroup.CSA
import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Conjugacy
import TauCeti.GroupTheory.GroupAlgGeom.Separated
import TauCeti.GroupTheory.NoncommPiCoprod

/-!
# The solutions of a level over a group are covered by a tower

Let `L` be a level of a triangular quasi-quadratic system, in the variables `X` and with
coefficients in a group `K`, and let `f : K →* H` read the coefficients in a group `H`. The
`H`-points of `L` are the solutions in `H` of the equations of `L` with coefficients `f c`. This
file shows, for the levels of types (2)–(4), that they are *covered by a normalized tower over
`H`*: there are a tower `T` over `H` and a point `q ∈ T^X` of `L` such that every `H`-point of `L`
is `ρ ∘ q` for a homomorphism `ρ : T → H` over `H`.

Only `H`-points are covered: a solution in a group `F` of the level with its coefficients read in
`F` through a homomorphism `H → F` need not factor through the tower.

## Main results

* `TauCeti.LimitGroup.NTQ.Level.exists_tower_empty`,
  `TauCeti.LimitGroup.NTQ.Level.exists_tower_abelian`: the `H`-points of an empty or abelian level
  are covered by a tower over `H`.
* `TauCeti.LimitGroup.NTQ.Level.exists_tower_centralizer`: over a commutative transitive group
  `H`, the `H`-points of a centralizer level are covered by a tower over `H`.

## Implementation notes

The tower depends on the kind of the level:

* an empty level: the free level `H[X] = H ∗ F(X)`;
* an abelian level: the abelian level `H ∗ ℤ^X`;
* a centralizer level, over a commutative transitive group `H`: `H` itself when two nontrivial
  coefficients do not commute (then the only solution is trivial), the abelian level when all
  coefficients are `1`, and otherwise one quadratic level `y⁻¹ c y c⁻¹ = 1` for each variable,
  stacked, for a nontrivial coefficient `c`; the top carrier is separated by `H`, so the
  centralizer of `c` in it is abelian and the new letters commute.

A raw level of type (2) is thus normalized by quadratic conjugacy levels, not by an admissible
extension of a centralizer, which would need finitely generated abelian centralizers.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §5.6, proof of Theorem 6.
* [VAR-II] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. II:
  Systems in triangular quasi-quadratic form and description of residually free groups*,
  J. Algebra 200 (1998), §5, Lemmas 8–9.
-/

public section

open Monoid.Coprod Subgroup TauCeti.GroupAlgGeom Group
open scoped commutatorElement

universe u v

namespace TauCeti.LimitGroup.NTQ.Level

variable {K : Type v} [Group K] {H : Type u} [Group H] {X : Type u} [Finite X]

/-- The `H`-points of an empty level, that is all of `H^X`, are covered by a tower over `H`. -/
theorem exists_tower_empty (f : K →* H) :
    ∃ (T : Type u) (_ : Group T) (j : H →* T) (_ : Tower H T j) (q : X → T),
      q ∈ V (j.comp f) (empty : Level K X).equations ∧
        ∀ v ∈ V f (empty : Level K X).equations, ∃ ρ : GHom j (MonoidHom.id H), ⇑ρ ∘ q = v :=
  ⟨GX H X, inferInstance, inl, Tower.single (.free X), fun x ↦ inr (FreeGroup.of x), by simp,
    fun v _ ↦ ⟨evalGHom (.id H) v, funext fun x ↦ by simp⟩⟩

/-- The `H`-points of an abelian level, the pairwise commuting tuples, are covered by a tower over
`H`. -/
theorem exists_tower_abelian (f : K →* H) :
    ∃ (T : Type u) (_ : Group T) (j : H →* T) (_ : Tower H T j) (q : X → T),
      q ∈ V (j.comp f) (abelian : Level K X).equations ∧
        ∀ v ∈ V f (abelian : Level K X).equations, ∃ ρ : GHom j (MonoidHom.id H), ⇑ρ ∘ q = v := by
  let e := Finite.equivFin X
  refine ⟨Monoid.Coprod H (Fin (Nat.card X) → Multiplicative ℤ), inferInstance, inl,
    Tower.single (.abelian (Nat.card X)), fun x ↦ inr (Pi.mulSingle (e x) (.ofAdd 1)),
    mem_V_abelian.2 fun _ _ ↦ (Commute.all _ _).map inr, fun v hv ↦ ?_⟩
  exact ⟨⟨lift (.id H) (zpowersPiHom (v ∘ e.symm) fun _ _ ↦ mem_V_abelian.1 hv _ _),
    lift_apply_inl _ _⟩, funext fun x ↦ by simp⟩

/-! ### Centralizer levels -/

section Centralizer

open Quadratic.Standard

/-- Over `H` and for `c ≠ 1`, the tower of `n` stacked quadratic levels `yᵢ⁻¹ c yᵢ c⁻¹ = 1` has a
top carrier `T` separated by `H`, the letters `yᵢ` commute with `c` in `T`, and every tuple of
elements of `H` commuting with `c` is the image of `(y₁, …, yₙ)` under a homomorphism `T → H`
over `H`. -/
private theorem exists_tower_centralizerEquation {c : H} (hc : c ≠ 1) : ∀ n : ℕ,
    ∃ (T : Type u) (_ : Group T) (j : H →* T) (_ : Tower H T j) (q : Fin n → T),
      IsSeparatedBy j (MonoidHom.id H) ∧ (∀ i, Commute (q i) (j c)) ∧
        ∀ v : Fin n → H, (∀ i, Commute (v i) c) → ∃ ρ : GHom j (MonoidHom.id H), ⇑ρ ∘ q = v
  | 0 => ⟨H, inferInstance, .id H, .base, Fin.elim0, (IsDiscriminatedBy.self _).isSeparatedBy,
      fun i ↦ i.elim0, fun _ _ ↦ ⟨GHom.id _, funext fun i ↦ i.elim0⟩⟩
  | n + 1 => by
    obtain ⟨T, _, j, t, q, hsep, hq, hcov⟩ := exists_tower_centralizerEquation hc n
    have hjc : j c ≠ 1 := (map_ne_one_iff j t.injective).2 hc
    let S : Set (GX T PUnit.{u + 1}) := {(centralizerEquation .unit hjc).toWord}
    -- Each level is a coordinate group over the carrier below, so it is separated by `H`.
    have hsep' := (CoordGroup.isSeparatedBy_coeff (ι := .id T) S).comp j
    rw [MonoidHom.id_comp] at hsep'
    refine ⟨CoordGroup (.id T) S, inferInstance, (CoordGroup.coeff (.id T) S).comp j,
      t.cons (.quadratic PUnit (centralizerEquation .unit hjc) 1
        (mem_V_centralizerEquation.2 (.one_left _))),
      Fin.cons (CoordGroup.genericPoint (.id T) S .unit) (CoordGroup.coeff (.id T) S ∘ q),
      hsep'.trans hsep, fun i ↦ ?_, fun v hv ↦ ?_⟩
    · refine Fin.cases ?_ (fun i ↦ ?_) i
      · exact (mem_V_centralizerEquation (x := PUnit.unit) (hc := hjc)).1
          (CoordGroup.genericPoint_mem_V S)
      · simpa using (hq i).map (CoordGroup.coeff (.id T) S)
    · obtain ⟨ρ, hρ⟩ := hcov (Fin.tail v) fun i ↦ hv i.succ
      have hw : (fun _ ↦ j (v 0)) ∈ V (.id T) S := mem_V_centralizerEquation.2 ((hv 0).map j)
      refine ⟨⟨(ρ : T →* H).comp (CoordGroup.evalGHom _ hw : _ →* T), fun h ↦ ?_⟩,
        funext fun i ↦ Fin.cases ?_ (fun i ↦ ?_) i⟩
      · simp
      · simp
      · simpa [Fin.tail] using congrFun hρ i

/-- Over a commutative transitive group `H`, if a coefficient `c₀ ∈ U` with `f c₀ ≠ 1` commutes
with all the coefficients `f c`, `c ∈ U`, then the `H`-points of the centralizer level, the tuples
in the centralizer of `f c₀`, are covered by the stacked conjugacy levels
`y⁻¹ (f c₀) y (f c₀)⁻¹ = 1`. -/
private theorem exists_tower_centralizer_of_commute (hH : IsCommTransitive H) (f : K →* H)
    {U : Set K} (hU : U.Finite) {c₀ : K} (hc₀ : c₀ ∈ U) (hfc₀ : f c₀ ≠ 1)
    (hU' : ∀ c ∈ U, Commute (f c) (f c₀)) :
    ∃ (T : Type u) (_ : Group T) (j : H →* T) (_ : Tower H T j) (q : X → T),
      q ∈ V (j.comp f) (centralizer U hU : Level K X).equations ∧
        ∀ v ∈ V f (centralizer U hU : Level K X).equations, ∃ ρ : GHom j (MonoidHom.id H),
          ⇑ρ ∘ q = v := by
  obtain ⟨T, _, j, t, q, hT, hq, hcov⟩ := exists_tower_centralizerEquation hfc₀ (Nat.card X)
  -- The centralizer of `f c₀` is abelian in `T`, which is separated by `H`.
  have := hT.isMulCommutative_centralizer
    (isCommTransitive_iff_centralizer_isMulCommutative.1 hH _ hfc₀)
  have hmem {a : T} (ha : Commute a (j (f c₀))) : a ∈ Subgroup.centralizer {j (f c₀)} :=
    mem_centralizer_singleton_iff.2 ha.eq
  let e := Finite.equivFin X
  refine ⟨T, _, j, t, q ∘ e, mem_V_centralizer.2 ⟨fun x y ↦ ?_, fun x c hc ↦ ?_⟩,
    fun v hv ↦ ?_⟩
  · exact setLike_mul_comm (hmem (hq _)) (hmem (hq _))
  · exact setLike_mul_comm (hmem (hq _)) (hmem ((hU' c hc).map j))
  · obtain ⟨ρ, hρ⟩ := hcov (v ∘ e.symm) fun i ↦ (mem_V_centralizer.1 hv).2 _ c₀ hc₀
    exact ⟨ρ, funext fun x ↦ by simpa using congrFun hρ (e x)⟩

/-- Over a commutative transitive group `H`, the `H`-points of a centralizer level, the tuples of
pairwise commuting elements commuting with the coefficients, are covered by a tower over `H`. -/
theorem exists_tower_centralizer (hH : IsCommTransitive H) (f : K →* H) (U : Set K)
    (hU : U.Finite) :
    ∃ (T : Type u) (_ : Group T) (j : H →* T) (_ : Tower H T j) (q : X → T),
      q ∈ V (j.comp f) (centralizer U hU : Level K X).equations ∧
        ∀ v ∈ V f (centralizer U hU : Level K X).equations, ∃ ρ : GHom j (MonoidHom.id H),
          ⇑ρ ∘ q = v := by
  by_cases h₁ : ∀ c ∈ U, f c = 1
  · -- All coefficients are trivial: the points are those of the abelian level.
    obtain ⟨T, _, j, t, q, hq, hcov⟩ := exists_tower_abelian (X := X) f
    refine ⟨T, _, j, t, q, mem_V_centralizer.2 ⟨mem_V_abelian.1 hq, fun x c hc ↦ ?_⟩,
      fun v hv ↦ hcov v (mem_V_abelian.2 (mem_V_centralizer.1 hv).1)⟩
    simp [h₁ c hc]
  push Not at h₁
  obtain ⟨c₀, hc₀, hfc₀⟩ := h₁
  by_cases h₂ : ∀ c ∈ U, Commute (f c) (f c₀)
  · exact exists_tower_centralizer_of_commute hH f hU hc₀ hfc₀ h₂
  -- Two coefficients do not commute: the only point is trivial, covered by `H` itself.
  push Not at h₂
  obtain ⟨c₁, hc₁, hfc₁⟩ := h₂
  refine ⟨H, inferInstance, .id H, .base, 1,
    mem_V_centralizer.2 ⟨fun _ _ ↦ .one_left _, fun _ _ _ ↦ .one_left _⟩, fun v hv ↦ ?_⟩
  rw [eq_one_of_mem_V_centralizer hH hc₀ hc₁ hfc₁ hv]
  exact ⟨GHom.id _, by simp⟩

end Centralizer

/-! ### Examples -/

/-- Over `F(a, b)`, the solutions `x = aᵏ` of the centralizer level `[x, a] = 1` in one variable are
covered by a tower over `F(a, b)`: there is an element `q` commuting with `a` in a tower over
`F(a, b)` such that every power of `a` is the image of `q` under a homomorphism to `F(a, b)` over
`F(a, b)`. -/
example : ∃ (T : Type) (_ : Group T) (j : FreeGroup (Fin 2) →* T)
    (_ : Tower (FreeGroup (Fin 2)) T j) (q : T), ⁅q, j (.of 0)⁆ = 1 ∧
      ∀ k : ℤ, ∃ ρ : GHom j (MonoidHom.id (FreeGroup (Fin 2))), ρ q = .of 0 ^ k := by
  obtain ⟨T, _, j, t, q, hq, hcov⟩ := exists_tower_centralizer (X := PUnit)
    IsFreeGroup.isCommTransitive (.id (FreeGroup (Fin 2))) {.of 0} (Set.finite_singleton _)
  refine ⟨T, _, j, t, q .unit, commutatorElement_eq_one_iff_commute.2
    ((mem_V_centralizer.1 hq).2 .unit _ rfl), fun k ↦ ?_⟩
  obtain ⟨ρ, hρ⟩ := hcov (fun _ ↦ .of 0 ^ k) <| mem_V_centralizer.2
    ⟨fun _ _ ↦ .refl _, fun _ c hc ↦ by rw [Set.mem_singleton_iff.1 hc]; exact .zpow_left rfl k⟩
  exact ⟨ρ, congrFun hρ .unit⟩

end TauCeti.LimitGroup.NTQ.Level
