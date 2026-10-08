/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Basic

/-!
# Preprojective algebras of quivers without sinks

Let `Q` be a finite quiver without sinks, that is, every vertex is the tail of an arrow of `Q`, and
let `Π = Π_k(Q)` be its preprojective algebra over a commutative ring `k`. This file proves that
for every arrow `a : v ⟶ w` of `Q`, left multiplication by `a` is injective on `e_v Π`.

Consequently the left-hand map `y ↦ (ε_b b* y)_b` of the Koszul complex

```text
0 ⟶ e_v Π ⟶ ⨁_{b : i ⟶ v} e_i Π ⟶ e_v Π ⟶ S_v ⟶ 0
```

of `TauCeti.RepresentationTheory.Quiver.Preprojective.KoszulComplex` is injective. Together with
the exactness at the other terms proved there, the complex is a projective resolution of the vertex
module `S_v`, for every vertex `v` and every commutative ring `k`.

The hypothesis is on the orientation, while `Π` does not depend on the orientation up to
isomorphism (`TauCeti.reorientPreprojectiveAlgebraEquiv`). A connected graph admits an orientation
without sinks exactly when it is not a tree, so the non-Dynkin trees, such as `D~ₙ` and `E₆~`,
`E₇~`, `E₈~`, are not covered here.

## Main results

* `TauCeti.preprojectiveMk_ofArrow_mul_eq_zero_iff`: for `y ∈ e_v Π` and an arrow `a` of `Q` out of
  `v`, `a y = 0` exactly when `y = 0`.
* `TauCeti.forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff`: **exactness of the Koszul
  complex at its left end**: `b* y = 0` for every arrow `b` of the doubled quiver into `v` exactly
  when `y = 0`.

## Implementation notes

Choose an arrow `α_u : u ⟶ t(u)` of `Q` at every vertex `u` and write `β_u = α_u*`. The local
relation at `u` (`TauCeti.localPreprojectiveRelator_eq_sum_ofArrow_mul`) solves for one backtrack,
`β_u α_u = ∑_{b ≠ β_u} ε_b b b*`, the sum over the other arrows `b` of the doubled quiver into `u`.
No `α` is a `β`, so the leading words `β_u α_u` of these rewriting rules never overlap, and as in
Bergman's diamond lemma the rules define a left module directly. Its underlying `k`-module is free
on the paths of the doubled quiver, and an arrow `c` acts on a path `p` by appending `c`, except
that `β_u` acts on a path ending in `α_u` by the right-hand side of the rule, computed recursively
on the shorter path. This action respects the local relations, so `Π` acts. The class map from
paths to `Π` is `Π`-linear and recovers `y` from the action of `y` on the trivial paths, so the
action is faithful. Since `α_v` acts on the paths ending at `v` by appending `α_v`, it acts
injectively there, and so does `α_v` on `e_v Π`. Choosing `α_v = a` gives the result.

The module is assembled by `TauCeti.PathAlgebra.liftAlgHom` on the product of the vertex
components rather than through `TauCeti.QuiverRep`, whose representations are over a field: the
argument works over every commutative ring.

## References

* G. M. Bergman, *The diamond lemma for ring theory*, Adv. Math. 29 (1978), for the construction of
  a module from a rewriting system without ambiguities.
* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, Math.
  Res. Lett. 14 (2007), Sections 2 and 3, for the Koszul complex and the Koszulity of the
  preprojective algebras of non-Dynkin quivers.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v} Q] (σ : ∀ v : Q, Σ w : Q, (v ⟶ w))

/-! ### The rewriting rules -/

/-- The head `t(y)` of the chosen arrow at `y`, as a vertex of the doubled quiver. -/
private def chosenTarget (y : Symmetrify Q) : Symmetrify Q :=
  Symmetrify.of.obj (σ y).1

/-- The chosen arrow `α_y : y ⟶ t(y)`, an arrow of `Q` read in the doubled quiver. -/
private def chosenArrow (y : Symmetrify Q) : y ⟶ chosenTarget σ y :=
  Symmetrify.of.map (V := Q) (σ y).2

/-- The two-arrow word `c e` is a leading word `β_y α_y`: `e` is the chosen arrow `α_y` and `c` is
its reverse. -/
private def IsBacktrack {y x z : Symmetrify Q} (e : y ⟶ x) (c : x ⟶ z) : Prop :=
  (⟨x, e⟩ : Σ x, y ⟶ x) = ⟨_, chosenArrow σ y⟩ ∧ (⟨z, c⟩ : Σ z, x ⟶ z) = ⟨y, reverse e⟩

/-- The paths of the doubled quiver ending at `x`. -/
private abbrev Word (x : Symmetrify Q) := Σ a : Symmetrify Q, Path a x

/-- Appending the arrow `b`, extended linearly. -/
private noncomputable def append {i y : Symmetrify Q} (b : i ⟶ y) :
    (Word i →₀ k) →ₗ[k] (Word y →₀ k) :=
  Finsupp.lmapDomain k k fun w => ⟨w.1, w.2.cons b⟩

private theorem append_single {i y : Symmetrify Q} (b : i ⟶ y) (w : Word i) (r : k) :
    append k b (Finsupp.single w r) = Finsupp.single ⟨w.1, w.2.cons b⟩ r := by
  rw [append, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- A chosen arrow `α_v` is never the reverse `β_u` of a chosen arrow: the former is an arrow of
`Q`, the latter the reverse of one. -/
private theorem sigma_chosenArrow_ne (v : Symmetrify Q) :
    (⟨v, chosenArrow σ v⟩ : Σ i, i ⟶ chosenTarget σ v) ≠
      ⟨_, reverse (chosenArrow σ (chosenTarget σ v))⟩ := by
  intro h
  -- An arrow of the doubled quiver is a sum; `α_v` is a left summand and `β_u` a right one, so
  -- `Sum.isLeft` evaluates to `true` on the left of `h` and to `false` on its right.
  have := congrArg (fun s : Σ i, i ⟶ chosenTarget σ v => Sum.isLeft s.2) h
  exact Bool.noConfusion this

/-- A chosen arrow is an arrow of `Q`, so it has sign `1`. -/
private theorem doubledArrowSign_chosenArrow (y : Symmetrify Q) :
    doubledArrowSign k (chosenArrow σ y) = 1 :=
  doubledArrowSign_inl k (σ y).2

/-- Appending an arrow is injective on paths, hence on their linear combinations. -/
private theorem append_injective {i y : Symmetrify Q} (b : i ⟶ y) :
    Function.Injective (append k b) := by
  intro n n' h
  rw [append, Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply] at h
  refine Finsupp.mapDomain_injective (fun w w' hw => ?_) h
  obtain ⟨a, p⟩ := w
  obtain ⟨a', p'⟩ := w'
  obtain ⟨rfl, hp⟩ := Sigma.mk.inj_iff.1 hw
  obtain rfl := eq_of_heq (Path.heq_of_cons_eq_cons (eq_of_heq hp))
  rfl

variable [Fintype Q] [∀ i j : Q, Fintype (i ⟶ j)]

open scoped Classical in
/-- The action `p ↦ c · p` of an arrow `c` on a path `p` ending at its tail: append `c`, unless `p`
ends in `α_y` and `c = β_y`, in which case `β_y α_y q` is rewritten as
`∑_{b ≠ β_y} ε_b b (b* · q)`, recursively on the shorter path `q`. -/
private noncomputable def act : ∀ {a y : Symmetrify Q}, Path a y → ∀ {z : Symmetrify Q},
    (y ⟶ z) → (Word z →₀ k)
  | a, _, .nil, _, c => Finsupp.single ⟨a, Path.nil.cons c⟩ 1
  | a, _, .cons (b := y) p e, _, c =>
    if h : IsBacktrack σ e c then
      cast (congrArg (fun t => Word t →₀ k) (congrArg Sigma.fst h.2).symm)
        (∑ s ∈ ({⟨_, reverse (chosenArrow σ y)⟩} : Finset (Σ i, i ⟶ y))ᶜ,
          doubledArrowSign k s.2 • append k s.2 (act p (reverse s.2)))
    else Finsupp.single ⟨a, (p.cons e).cons c⟩ 1

private theorem act_nil {a z : Symmetrify Q} (c : a ⟶ z) :
    act k σ (Path.nil : Path a a) c = Finsupp.single ⟨a, Path.nil.cons c⟩ 1 := by
  rw [act]

private theorem act_cons_of_not {a y x z : Symmetrify Q} (p : Path a y) (e : y ⟶ x)
    (c : x ⟶ z) (h : ¬ IsBacktrack σ e c) :
    act k σ (p.cons e) c = Finsupp.single ⟨a, (p.cons e).cons c⟩ 1 := by
  rw [act, dite_eq_right h]

open scoped Classical in
private theorem act_cons_of_isBacktrack {a y x z : Symmetrify Q} (p : Path a y) (e : y ⟶ x)
    (c : x ⟶ z) (h : IsBacktrack σ e c) :
    act k σ (p.cons e) c =
      cast (congrArg (fun t => Word t →₀ k) (congrArg Sigma.fst h.2).symm)
        (∑ s ∈ ({⟨_, reverse (chosenArrow σ y)⟩} : Finset (Σ i, i ⟶ y))ᶜ,
          doubledArrowSign k s.2 • append k s.2 (act k σ p (reverse s.2))) := by
  rw [act, dite_eq_left h]

open scoped Classical in
private theorem act_cons_backtrack {a y : Symmetrify Q} (p : Path a y) :
    act k σ (p.cons (chosenArrow σ y)) (reverse (chosenArrow σ y)) =
      ∑ s ∈ ({⟨_, reverse (chosenArrow σ y)⟩} : Finset (Σ i, i ⟶ y))ᶜ,
        doubledArrowSign k s.2 • append k s.2 (act k σ p (reverse s.2)) := by
  rw [act_cons_of_isBacktrack k σ p _ _ ⟨rfl, rfl⟩, cast_eq]

/-- An arrow which is not a `β` acts by appending it. -/
private theorem act_eq_single {a y z : Symmetrify Q} (p : Path a y) (c : y ⟶ z)
    (hc : (⟨y, c⟩ : Σ y, y ⟶ z) ≠ ⟨_, reverse (chosenArrow σ z)⟩) :
    act k σ p c = Finsupp.single ⟨a, p.cons c⟩ 1 := by
  cases p with
  | nil => exact act_nil k σ c
  | cons p e =>
    refine act_cons_of_not k σ p e c fun h => hc ?_
    obtain ⟨h1, h2⟩ := h
    cases h2
    cases h1
    rfl

private theorem act_chosenArrow {a v : Symmetrify Q} (p : Path a v) :
    act k σ p (chosenArrow σ v) = Finsupp.single ⟨a, p.cons (chosenArrow σ v)⟩ 1 :=
  act_eq_single k σ p _ (sigma_chosenArrow_ne σ v)

/-- The action of an arrow on linear combinations of paths. -/
private noncomputable def arrowMap {y z : Symmetrify Q} (c : y ⟶ z) :
    (Word y →₀ k) →ₗ[k] (Word z →₀ k) :=
  Finsupp.linearCombination k fun w => act k σ w.2 c

private theorem arrowMap_single {y z : Symmetrify Q} (c : y ⟶ z) (w : Word y) (r : k) :
    arrowMap k σ c (Finsupp.single w r) = r • act k σ w.2 c := by
  rw [arrowMap, Finsupp.linearCombination_single]

private theorem arrowMap_eq_append {y z : Symmetrify Q} (c : y ⟶ z)
    (hc : (⟨y, c⟩ : Σ y, y ⟶ z) ≠ ⟨_, reverse (chosenArrow σ z)⟩) :
    arrowMap k σ c = append k c := by
  refine Finsupp.lhom_ext fun w r => ?_
  rw [arrowMap_single, append_single, act_eq_single k σ _ c hc, Finsupp.smul_single_one]

/-! ### The action of the path algebra -/

/-- The action of a path, composing the actions of its arrows. -/
private noncomputable def pathMap : ∀ {a b : Symmetrify Q}, Path a b →
    ((Word a →₀ k) →ₗ[k] (Word b →₀ k))
  | _, _, .nil => LinearMap.id
  | _, _, .cons p c => arrowMap k σ c ∘ₗ pathMap p

private theorem pathMap_comp {a b c : Symmetrify Q} (q : Path c a) (p : Path a b) :
    pathMap k σ (q.comp p) = pathMap k σ p ∘ₗ pathMap k σ q := by
  induction p with
  | nil => rw [Path.comp_nil, pathMap, LinearMap.id_comp]
  | cons p e ih => rw [Path.comp_cons, pathMap, pathMap, ih, LinearMap.comp_assoc]

variable (Q) in
/-- The module on which the doubled path algebra acts: linear combinations of paths, split by their
endpoint. -/
private abbrev Vec := (x : Symmetrify Q) → (Word x →₀ k)

open scoped Classical in
/-- The endomorphism by which a path acts. -/
private noncomputable def pathEnd (x : TauCeti.Quiver.TotalPath (Symmetrify Q)) :
    Module.End k (Vec k Q) :=
  LinearMap.single k (fun x => Word x →₀ k) x.2.1 ∘ₗ pathMap k σ x.2.2 ∘ₗ LinearMap.proj x.1

open scoped Classical in
private theorem pathEnd_apply (x : TauCeti.Quiver.TotalPath (Symmetrify Q)) (m : Vec k Q) :
    pathEnd k σ x m = Pi.single x.2.1 (pathMap k σ x.2.2 (m x.1)) := (rfl)

private theorem pathEnd_mul_pathEnd {a b c : Symmetrify Q} (p : Path a b) (q : Path c a) :
    pathEnd k σ ⟨a, b, p⟩ * pathEnd k σ ⟨c, a, q⟩ = pathEnd k σ ⟨c, b, q.comp p⟩ := by
  classical
  refine LinearMap.ext fun m => ?_
  rw [Module.End.mul_apply, pathEnd_apply, pathEnd_apply, pathEnd_apply, pathMap_comp,
    Pi.single_eq_same, LinearMap.comp_apply]

private theorem pathEnd_mul_pathEnd_of_ne {x y : TauCeti.Quiver.TotalPath (Symmetrify Q)}
    (h : y.2.1 ≠ x.1) : pathEnd k σ x * pathEnd k σ y = 0 := by
  classical
  refine LinearMap.ext fun m => ?_
  rw [Module.End.mul_apply, pathEnd_apply, pathEnd_apply, Pi.single_eq_of_ne h.symm, map_zero,
    Pi.single_zero, LinearMap.zero_apply]

private theorem sum_pathEnd_nil [Fintype (Symmetrify Q)] :
    ∑ v : Symmetrify Q, pathEnd k σ ⟨v, v, Path.nil⟩ = 1 := by
  classical
  refine LinearMap.ext fun m => ?_
  simp only [LinearMap.sum_apply, pathEnd_apply, pathMap, LinearMap.id_apply,
    Module.End.one_apply, Finset.univ_sum_single]

/-- The action of the doubled path algebra. -/
private noncomputable def toEnd : pathAlgebra k (Symmetrify Q) →ₐ[k] Module.End k (Vec k Q) :=
  liftAlgHom k (pathEnd k σ) (pathEnd_mul_pathEnd k σ) (pathEnd_mul_pathEnd_of_ne k σ)
    (letI := Fintype.ofFinite (Symmetrify Q); sum_pathEnd_nil k σ)

/-! ### The local relations act by zero -/

open scoped Classical in
/-- The local relation at `u` acts by zero on a path ending at `u`: its `β_u` term is the rewritten
backtrack `β_u α_u`, and it cancels the other terms. -/
private theorem sum_arrowMap_act_reverse {a u : Symmetrify Q} (p : Path a u) :
    ∑ s : Σ i, i ⟶ u, doubledArrowSign k s.2 • arrowMap k σ s.2 (act k σ p (reverse s.2)) =
      0 := by
  rw [Fintype.sum_eq_add_sum_compl ⟨_, reverse (chosenArrow σ u)⟩, add_eq_zero_iff_neg_eq,
    reverse_reverse, act_chosenArrow, arrowMap_single, one_smul, act_cons_backtrack,
    doubledArrowSign_reverse, doubledArrowSign_chosenArrow, neg_one_smul, neg_neg]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [arrowMap_eq_append k σ s.2 (Finset.mem_compl.1 hs <| Finset.mem_singleton.2 ·)]

private theorem sum_arrowMap_comp_arrowMap_reverse (u : Symmetrify Q) :
    ∑ s : Σ i, i ⟶ u, doubledArrowSign k s.2 • (arrowMap k σ s.2 ∘ₗ arrowMap k σ (reverse s.2)) =
      0 := by
  refine Finsupp.lhom_ext fun w r => ?_
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, arrowMap_single,
    map_smul, LinearMap.zero_apply]
  simp only [smul_comm (doubledArrowSign k _) r, ← Finset.smul_sum, sum_arrowMap_act_reverse,
    smul_zero]

open scoped Classical in
private theorem toEnd_ofArrow_apply {i j : Symmetrify Q} (b : i ⟶ j) (m : Vec k Q) :
    toEnd k σ (ofArrow b) m = Pi.single j (arrowMap k σ b (m i)) := by
  rw [ofArrow_eq_ofPath, toEnd, liftAlgHom_ofPath, pathEnd_apply, Hom.toPath, pathMap, pathMap,
    LinearMap.comp_id]

open scoped Classical in
private theorem toEnd_vertexIdempotent_apply (v : Symmetrify Q) (m : Vec k Q) :
    toEnd k σ (vertexIdempotent k v) m = Pi.single v (m v) := by
  rw [vertexIdempotent_eq_ofPath, toEnd, liftAlgHom_ofPath, pathEnd_apply, pathMap,
    LinearMap.id_apply]

private theorem toEnd_localPreprojectiveRelator (u : Q) :
    toEnd k σ (localPreprojectiveRelator k u) = 0 := by
  classical
  refine LinearMap.ext fun m => ?_
  have h := LinearMap.congr_fun (sum_arrowMap_comp_arrowMap_reverse k σ (Symmetrify.of.obj u))
    (m (Symmetrify.of.obj u))
  rw [localPreprojectiveRelator_eq_sum_ofArrow_mul]
  simp only [map_sum, map_mul, map_smul, LinearMap.sum_apply, Module.End.mul_apply,
    LinearMap.smul_apply, toEnd_ofArrow_apply, Pi.single_eq_same, LinearMap.zero_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.zero_apply, Fintype.sum_sigma] at h
  simp only [← LinearMap.coe_single k (fun x => Word x →₀ k)]
  calc _ = LinearMap.single k (fun x => Word x →₀ k) (Symmetrify.of.obj u)
        (∑ i, ∑ b : i ⟶ Symmetrify.of.obj u, doubledArrowSign k b •
          arrowMap k σ b (arrowMap k σ (reverse b) (m (Symmetrify.of.obj u)))) := by
        simp only [map_sum, map_smul]
    _ = 0 := by rw [h, map_zero]

/-- The action of the preprojective algebra. -/
private noncomputable def toEndPreprojective :
    preprojectiveAlgebra k Q →ₐ[k] Module.End k (Vec k Q) :=
  preprojectiveLiftOfForallLocalPreprojectiveRelator (toEnd k σ)
    (toEnd_localPreprojectiveRelator k σ)

private theorem toEndPreprojective_preprojectiveMk (f : pathAlgebra k (Symmetrify Q)) :
    toEndPreprojective k σ (preprojectiveMk k Q f) = toEnd k σ f :=
  preprojectiveLiftOfForallLocalPreprojectiveRelator_preprojectiveMk _ _ f

/-! ### Reading paths back in the preprojective algebra -/

open scoped Classical in
/-- The local relation at `v`, solved for the backtrack `β_v α_v` along the chosen arrow. -/
private theorem preprojectiveMk_backtrack (v : Q) :
    preprojectiveMk k Q (ofArrow (reverse (chosenArrow σ (Symmetrify.of.obj v))) *
      ofArrow (chosenArrow σ (Symmetrify.of.obj v))) =
      ∑ s ∈ ({⟨_, reverse (chosenArrow σ (Symmetrify.of.obj v))⟩} :
          Finset (Σ i, i ⟶ Symmetrify.of.obj v))ᶜ,
        doubledArrowSign k s.2 • preprojectiveMk k Q (ofArrow s.2 * ofArrow (reverse s.2)) := by
  have h : ∑ s : Σ i, i ⟶ Symmetrify.of.obj v,
      doubledArrowSign k s.2 • preprojectiveMk k Q (ofArrow s.2 * ofArrow (reverse s.2)) = 0 := by
    rw [Fintype.sum_sigma]
    simpa only [localPreprojectiveRelator_eq_sum_ofArrow_mul, map_sum, mul_smul_comm, map_smul]
      using preprojectiveMk_localPreprojectiveRelator k v
  rw [Fintype.sum_eq_add_sum_compl ⟨_, reverse (chosenArrow σ (Symmetrify.of.obj v))⟩,
    add_eq_zero_iff_neg_eq] at h
  simpa only [reverse_reverse, doubledArrowSign_reverse, doubledArrowSign_chosenArrow,
    neg_one_smul, neg_neg] using h

/-- The class in `Π` of a linear combination of paths. -/
private noncomputable def readOff (x : Symmetrify Q) :
    (Word x →₀ k) →ₗ[k] preprojectiveAlgebra k Q :=
  Finsupp.linearCombination k fun w => preprojectiveMk k Q (ofPath ⟨w.1, x, w.2⟩)

private theorem readOff_single (x : Symmetrify Q) (w : Word x) (r : k) :
    readOff k x (Finsupp.single w r) = r • preprojectiveMk k Q (ofPath ⟨w.1, x, w.2⟩) :=
  Finsupp.linearCombination_single _ _ _

private theorem readOff_append {i y : Symmetrify Q} (b : i ⟶ y) (n : Word i →₀ k) :
    readOff k y (append k b n) = preprojectiveMk k Q (ofArrow b) * readOff k i n := by
  induction n using Finsupp.induction_linear with
  | zero => simp only [map_zero, mul_zero]
  | add n n' hn hn' => rw [map_add, map_add, hn, hn', map_add, mul_add]
  | single w r =>
    rw [append_single, readOff_single, readOff_single, mul_smul_comm, ← map_mul,
      ofArrow_mul_ofPath]

/-- The action of an arrow is left multiplication by it, read in `Π`. -/
private theorem readOff_act {a y z : Symmetrify Q} (p : Path a y) (c : y ⟶ z) :
    readOff k z (act k σ p c) =
      preprojectiveMk k Q (ofArrow c) * preprojectiveMk k Q (ofPath ⟨a, y, p⟩) := by
  classical
  induction p generalizing z with
  | nil => rw [act_nil, readOff_single, one_smul, ← map_mul, ofArrow_mul_ofPath]
  | @cons b x p e ih =>
    by_cases h : IsBacktrack σ e c
    · obtain ⟨h1, h2⟩ := h
      cases h2
      cases h1
      obtain ⟨v, rfl⟩ : ∃ v : Q, Symmetrify.of.obj v = b := ⟨b, rfl⟩
      rw [act_cons_backtrack, map_sum, ← ofArrow_mul_ofPath, map_mul, ← mul_assoc, ← map_mul,
        preprojectiveMk_backtrack, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [map_smul, readOff_append, ih, smul_mul_assoc, map_mul, mul_assoc]
    · rw [act_cons_of_not k σ p e c h, readOff_single, one_smul, ← map_mul, ofArrow_mul_ofPath]

private theorem readOff_arrowMap {y z : Symmetrify Q} (c : y ⟶ z) (n : Word y →₀ k) :
    readOff k z (arrowMap k σ c n) = preprojectiveMk k Q (ofArrow c) * readOff k y n := by
  induction n using Finsupp.induction_linear with
  | zero => simp only [map_zero, mul_zero]
  | add n n' hn hn' => rw [map_add, map_add, hn, hn', map_add, mul_add]
  | single w r =>
    rw [arrowMap_single, map_smul, readOff_act, readOff_single, mul_smul_comm]

private theorem readOff_pathMap {a b : Symmetrify Q} (p : Path a b) (n : Word a →₀ k) :
    readOff k b (pathMap k σ p n) = preprojectiveMk k Q (ofPath ⟨a, b, p⟩) * readOff k a n := by
  induction p with
  | nil =>
    induction n using Finsupp.induction_linear with
    | zero => simp only [map_zero, mul_zero]
    | add n n' hn hn' => rw [map_add, map_add, hn, hn', map_add, mul_add]
    | single w r =>
      rw [pathMap, LinearMap.id_apply, readOff_single, mul_smul_comm, ← map_mul,
        ofPath_mul_ofPath_of_comp, Path.comp_nil]
  | cons p c ih =>
    rw [pathMap, LinearMap.comp_apply, readOff_arrowMap, ih, ← mul_assoc, ← map_mul,
      ofArrow_mul_ofPath]

variable (Q) in
/-- The vector of trivial paths. -/
private noncomputable def unitVec : Vec k Q := fun x => Finsupp.single ⟨x, Path.nil⟩ 1

/-- The class in `Π` of a vector of linear combinations of paths. -/
private noncomputable def readOffAll : Vec k Q →ₗ[k] preprojectiveAlgebra k Q :=
  ∑ x, readOff k x ∘ₗ LinearMap.proj x

open scoped Classical in
private theorem readOffAll_single (x : Symmetrify Q) (n : Word x →₀ k) :
    readOffAll k (Pi.single x n) = readOff k x n := by
  rw [readOffAll, LinearMap.sum_apply, Finset.sum_eq_single x, LinearMap.comp_apply,
    LinearMap.proj_apply, Pi.single_eq_same]
  · intro x' _ hx'
    rw [LinearMap.comp_apply, LinearMap.proj_apply, Pi.single_eq_of_ne hx', map_zero]
  · exact fun h => absurd (Finset.mem_univ x) h

private theorem readOffAll_toEnd_unitVec (f : pathAlgebra k (Symmetrify Q)) :
    readOffAll k (toEnd k σ f (unitVec k Q)) = preprojectiveMk k Q f := by
  classical
  induction f using PathAlgebra.induction_linear with
  | zero => rw [map_zero, LinearMap.zero_apply, map_zero, map_zero]
  | add f f' hf hf' => rw [map_add, LinearMap.add_apply, map_add, hf, hf', map_add]
  | single x c =>
    obtain ⟨a, b, p⟩ := x
    have haction :
        toEnd k σ (ofPath ⟨a, b, p⟩) (unitVec k Q) =
          Pi.single b (pathMap k σ p (Finsupp.single ⟨a, Path.nil⟩ 1)) := by
      rw [toEnd, liftAlgHom_ofPath, pathEnd_apply, unitVec]
    have hread :
        readOff k b (pathMap k σ p (Finsupp.single ⟨a, Path.nil⟩ 1)) =
          preprojectiveMk k Q (ofPath ⟨a, b, p⟩) := by
      rw [readOff_pathMap, readOff_single, one_smul, ← map_mul, ofPath_mul_ofPath_of_comp,
        Path.nil_comp]
    rw [single_eq_smul_ofPath, map_smul, LinearMap.smul_apply, haction, map_smul,
      readOffAll_single, hread, map_smul]

/-- **The action is faithful**: `y` is read back from its action on the trivial paths. -/
private theorem readOffAll_toEndPreprojective_unitVec (y : preprojectiveAlgebra k Q) :
    readOffAll k (toEndPreprojective k σ y (unitVec k Q)) = y := by
  obtain ⟨f, rfl⟩ := preprojectiveMk_surjective k Q y
  rw [toEndPreprojective_preprojectiveMk, readOffAll_toEnd_unitVec]

/-! ### Injectivity -/

/-- Left multiplication by the chosen arrow `α_v` is injective on `e_v Π`, because `α_v` acts on the
paths ending at `v` by appending it. -/
private theorem eq_zero_of_chosenArrow_mul_eq_zero (v : Q) {y : preprojectiveAlgebra k Q}
    (hy : preprojectiveMk k Q (doubledVertexIdempotent k v) * y = y)
    (h : preprojectiveMk k Q (ofArrow (chosenArrow σ (Symmetrify.of.obj v))) * y = 0) :
    y = 0 := by
  classical
  set m := toEndPreprojective k σ y (unitVec k Q) with hm_def
  have hm : m = Pi.single (Symmetrify.of.obj v) (m (Symmetrify.of.obj v)) := by
    conv_lhs => rw [hm_def, ← hy, map_mul, Module.End.mul_apply, ← hm_def,
      toEndPreprojective_preprojectiveMk, doubledVertexIdempotent_def,
      toEnd_vertexIdempotent_apply]
  have hmv : m (Symmetrify.of.obj v) = 0 := by
    have h1 := congrArg (fun z => toEndPreprojective k σ z (unitVec k Q)) h
    simp only [map_mul, Module.End.mul_apply, map_zero, LinearMap.zero_apply, ← hm_def,
      toEndPreprojective_preprojectiveMk, toEnd_ofArrow_apply, Pi.single_eq_zero_iff] at h1
    rw [arrowMap_eq_append k σ _ (sigma_chosenArrow_ne σ _)] at h1
    exact append_injective k _ (h1.trans (map_zero _).symm)
  rw [← readOffAll_toEndPreprojective_unitVec k σ y, ← hm_def, hm, hmv, Pi.single_zero, map_zero]

omit σ

/-- **An arrow of a quiver without sinks acts injectively on `e_v Π`.** If every vertex of `Q` is
the tail of an arrow, `a : v ⟶ w` is an arrow of `Q` and `y = e_v y`, then `a y = 0` exactly when
`y = 0`. -/
theorem preprojectiveMk_ofArrow_mul_eq_zero_iff (hQ : ∀ u : Q, ∃ w, Nonempty (u ⟶ w)) {v w : Q}
    (a : v ⟶ w) {y : preprojectiveAlgebra k Q}
    (hy : preprojectiveMk k Q (doubledVertexIdempotent k v) * y = y) :
    preprojectiveMk k Q (ofArrow (Symmetrify.of.map a)) * y = 0 ↔ y = 0 := by
  classical
  refine ⟨fun h => ?_, fun h => by rw [h, mul_zero]⟩
  -- Choose an outgoing arrow at every vertex, taking `a` at `v`.
  let σ : ∀ u : Q, Σ w : Q, (u ⟶ w) :=
    Function.update (fun u => ⟨(hQ u).choose, (hQ u).choose_spec.some⟩) v ⟨w, a⟩
  have hσ : σ v = ⟨w, a⟩ := Function.update_self ..
  -- The chosen arrow at `v` is `a`, read in the doubled quiver.
  have ha : ∀ s : Σ w : Q, (v ⟶ w), s = ⟨w, a⟩ →
      (ofArrow (Symmetrify.of.map s.2) : pathAlgebra k (Symmetrify Q)) =
        ofArrow (Symmetrify.of.map a) := by
    rintro _ rfl
    rfl
  -- `chosenArrow σ (Symmetrify.of.obj v)` unfolds to `Symmetrify.of.map (σ v).2`.
  exact eq_zero_of_chosenArrow_mul_eq_zero k σ v hy
    ((congrArg (fun f => preprojectiveMk k Q f * y) (ha (σ v) hσ)).trans h)

/-- **Exactness of the Koszul complex at its left end, for a quiver without sinks.** If every vertex
of `Q` is the tail of an arrow and `y = e_v y`, then `b* y = 0` for every arrow `b` of the doubled
quiver into `v` exactly when `y = 0`: the map `y ↦ (ε_b b* y)_b` of
`TauCeti.sum_preprojectiveMk_ofArrow_mul_eq_zero_iff` is injective. -/
theorem forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff
    (hQ : ∀ u : Q, ∃ w, Nonempty (u ⟶ w)) (v : Q) {y : preprojectiveAlgebra k Q}
    (hy : preprojectiveMk k Q (doubledVertexIdempotent k v) * y = y) :
    (∀ (i : Symmetrify Q) (b : i ⟶ Symmetrify.of.obj v),
      preprojectiveMk k Q (ofArrow (Quiver.reverse b)) * y = 0) ↔ y = 0 := by
  refine ⟨fun h => ?_, fun h i b => by rw [h, mul_zero]⟩
  obtain ⟨w, ⟨a⟩⟩ := hQ v
  refine (preprojectiveMk_ofArrow_mul_eq_zero_iff k hQ a hy).1 ?_
  simpa only [reverse_reverse] using h _ (Quiver.reverse (Symmetrify.of.map a))

end TauCeti
