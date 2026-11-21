/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.Basic

/-!
# The exact sequence of continuous nonabelian first cohomology

Let a topological group `G` act on topological groups `A'`, `A` and `A''`, and let

`1 → A' → A → A'' → 1`

be a short exact sequence of `G`-groups given by continuous `G`-equivariant homomorphisms
`i : A' →ₜ* A` and `p : A →ₜ* A''`, with `i` a topological embedding and `p` surjective
(`TauCeti.NonabelianH1.IsGroupExtension`). The prototype is a `G`-stable normal subgroup `A'` of
`A`, with the subspace topology, and the quotient `A'' = A ⧸ A'`. This file proves that the
sequence of pointed sets

`1 → A'ᴳ → Aᴳ → A''ᴳ → H¹(G, A') → H¹(G, A) → H¹(G, A'')`

is exact, and describes the fibres of `H¹(G, A') → H¹(G, A)`, which in the nonabelian setting are
not determined by the kernel.

The group `A''ᴳ` of fixed points acts on `H¹(G, A')`: for `c ∈ A''ᴳ` lifted to `b ∈ A`, the
cocycle `f` goes to the cocycle `g ↦ b * f g * (g • b)⁻¹`, which takes values in `A'` because
`p b` is fixed by `G`. The class of the result does not depend on the lift. The connecting map
`A''ᴳ → H¹(G, A')` sends `c` to the class of `g ↦ b⁻¹ * g • b`, the image of the base point under
`c⁻¹`.

* At `A''ᴳ`: the class `δ c` is the base point exactly when `c` lifts to `Aᴳ`; more generally the
  fibres of `δ` are the orbits of `Aᴳ` acting on `A''ᴳ` through `p`.
* At `H¹(G, A')`: two classes have the same image in `H¹(G, A)` exactly when they lie in one
  `A''ᴳ`-orbit. In particular the kernel of `H¹(G, A') → H¹(G, A)` is the image of the connecting
  map, the orbit of the base point.
* At `H¹(G, A)`: a class maps to the base point of `H¹(G, A'')` exactly when it comes from
  `H¹(G, A')`.

Together these identify the quotient of `H¹(G, A')` by the action of `A''ᴳ` with the neutral fibre
of `H¹(G, A) → H¹(G, A'')` (`TauCeti.NonabelianH1.IsGroupExtension.orbitRelQuotientEquiv`).

## Main definitions

* `TauCeti.NonabelianH1.IsGroupExtension G i p`: `1 → A' → A → A'' → 1` is a short exact
  sequence of topological `G`-groups.
* `TauCeti.NonabelianH1.IsGroupExtension.mulAction`: the action of `A''ᴳ` on `H¹(G, A')`.
* `TauCeti.NonabelianH1.IsGroupExtension.connecting`: the connecting map `A''ᴳ → H¹(G, A')`.
* `TauCeti.NonabelianH1.IsGroupExtension.orbitRelQuotientEquiv`: the orbits of `A''ᴳ` on
  `H¹(G, A')` are in bijection with the neutral fibre of `H¹(G, A) → H¹(G, A'')`.

## Main results

* `TauCeti.NonabelianH1.IsGroupExtension.apply_eq_one_iff_exists_mem_fixedPoints`: exactness at
  `Aᴳ`.
* `TauCeti.NonabelianH1.IsGroupExtension.connecting_eq_one_iff`: exactness at `A''ᴳ`.
* `TauCeti.NonabelianH1.IsGroupExtension.connecting_eq_connecting_iff`: the fibres of the
  connecting map are the `Aᴳ`-orbits.
* `TauCeti.NonabelianH1.IsGroupExtension.map_eq_map_iff`: the fibres of
  `H¹(G, A') → H¹(G, A)` are the `A''ᴳ`-orbits.
* `TauCeti.NonabelianH1.IsGroupExtension.map_eq_one_iff_mem_range_connecting`: exactness at
  `H¹(G, A')`.
* `TauCeti.NonabelianH1.IsGroupExtension.map_eq_one_iff_mem_range_map`: exactness at `H¹(G, A)`.

## References

* J.-P. Serre, *Galois Cohomology*, Springer, 1997, I.5.5, the cohomology exact sequence associated
  to a normal subgroup `A` of `B`, and the action of `H⁰(G, C)` on `H¹(G, A)`.
-/

public section

open Topology

namespace TauCeti

namespace NonabelianH1

variable {G A' A A'' : Type*} [Group G]
  [Group A'] [TopologicalSpace A'] [MulDistribMulAction G A']
  [Group A] [TopologicalSpace A] [MulDistribMulAction G A]
  [Group A''] [TopologicalSpace A''] [MulDistribMulAction G A'']

variable (G) in
/-- The sequence `1 → A' → A → A'' → 1` of topological `G`-groups given by `i` and `p` is a short
exact sequence: both maps are `G`-equivariant, `i` is a topological embedding, `p` is surjective,
and the image of `i` is the kernel of `p`. -/
structure IsGroupExtension (i : A' →ₜ* A) (p : A →ₜ* A'') : Prop where
  /-- The map `i : A' → A` is `G`-equivariant. -/
  map_smul_left (g : G) (a : A') : i (g • a) = g • i a
  /-- The map `p : A → A''` is `G`-equivariant. -/
  map_smul_right (g : G) (a : A) : p (g • a) = g • p a
  /-- The map `i : A' → A` is a topological embedding. -/
  isEmbedding : IsEmbedding i
  /-- The map `p : A → A''` is surjective. -/
  surjective : Function.Surjective p
  /-- The image of `i` is the kernel of `p`. -/
  mulExact : Function.MulExact i p

namespace IsGroupExtension

variable {i : A' →ₜ* A} {p : A →ₜ* A''} (hE : IsGroupExtension G i p)

include hE

/-- **Exactness at `Aᴳ`**: a fixed point of `A` maps to `1` in `A''` exactly when it comes from a
fixed point of `A'`. Since `i` is injective, `A'ᴳ → Aᴳ` is injective as well. -/
theorem apply_eq_one_iff_exists_mem_fixedPoints {a : A} (ha : a ∈ FixedPoints.subgroup G A) :
    p a = 1 ↔ ∃ a' ∈ FixedPoints.subgroup G A', i a' = a := by
  refine ⟨fun h ↦ ?_, fun ⟨a', _, ha'⟩ ↦ ha' ▸ hE.mulExact.apply_apply_eq_one a'⟩
  obtain ⟨a', rfl⟩ := (hE.mulExact a).mp h
  exact ⟨a', fun g ↦ hE.isEmbedding.injective (by rw [hE.map_smul_left, ha g]), rfl⟩

/-- The lift to `A` of a fixed point of `A''`, chosen by surjectivity of `p`. -/
private noncomputable def liftFixed (c : FixedPoints.subgroup G A'') : A :=
  (hE.surjective c).choose

private theorem apply_liftFixed (c : FixedPoints.subgroup G A'') : p (hE.liftFixed c) = c :=
  (hE.surjective c).choose_spec

private theorem apply_liftFixed_mem (c : FixedPoints.subgroup G A'') :
    p (hE.liftFixed c) ∈ FixedPoints.subgroup G A'' :=
  hE.apply_liftFixed c ▸ c.property

variable [TopologicalSpace G]

/-- The equivariance of `i`, stated as the compatibility of the pair
`(ContinuousMonoidHom.id G, i)` taken by `TauCeti.NonabelianH1.map`. -/
theorem compatible_left (g : G) (a : A') : i (ContinuousMonoidHom.id G g • a) = g • i a :=
  hE.map_smul_left g a

/-- The equivariance of `p`, stated as the compatibility of the pair
`(ContinuousMonoidHom.id G, p)` taken by `TauCeti.NonabelianH1.map`. -/
theorem compatible_right (g : G) (a : A) : p (ContinuousMonoidHom.id G g • a) = g • p a :=
  hE.map_smul_right g a

section Action

variable [ContinuousMul A] [ContinuousSMul G A]

/-- The cocycle `g ↦ b * f g * (g • b)⁻¹` of `A'`, for `b : A` whose image in `A''` is fixed by
`G`; its values lie in `A'` because they map to `p b * (g • p b)⁻¹ = 1`. -/
private noncomputable def smulCocycle (b : A) (hb : p b ∈ FixedPoints.subgroup G A'')
    (f : Cocycle G A') : Cocycle G A' :=
  ((f.map (ContinuousMonoidHom.id G) i hE.compatible_left).twist b⁻¹).liftOfMemRange i
    hE.isEmbedding hE.compatible_left fun g ↦ (hE.mulExact _).mp <| by
      simp [hE.map_smul_right, hb g, hE.mulExact.apply_apply_eq_one]

private theorem apply_smulCocycle (b : A) (hb : p b ∈ FixedPoints.subgroup G A'')
    (f : Cocycle G A') (g : G) :
    i (hE.smulCocycle b hb f g) = b * i (f g) * (g • b)⁻¹ := by
  simp [smulCocycle]

/-- The class of `hE.smulCocycle b hb f` depends only on `p b` and on the class of `f`. -/
private theorem mk_smulCocycle_eq {b b' : A} (hb : p b ∈ FixedPoints.subgroup G A'')
    (hb' : p b' ∈ FixedPoints.subgroup G A'') (hbb' : p b = p b') {f f' : Cocycle G A'}
    (hff' : NonabelianH1.mk f = NonabelianH1.mk f') :
    NonabelianH1.mk (hE.smulCocycle b hb f) = NonabelianH1.mk (hE.smulCocycle b' hb' f') := by
  obtain ⟨a, ha⟩ := mk_eq_mk_iff.mp hff'
  -- The conjugate of `i a * b'⁻¹ * b ∈ ker p` by `b` lies in the kernel of `p`, hence in `A'`.
  obtain ⟨x, hx⟩ := (hE.mulExact (b * (i a * b'⁻¹ * b) * b⁻¹)).mp <| by
    simp [hbb', hE.mulExact.apply_apply_eq_one]
  refine mk_eq_mk_iff.mpr ⟨x, fun g ↦ hE.isEmbedding.injective ?_⟩
  simp only [_root_.map_mul, _root_.map_inv, hE.map_smul_left, hx, hE.apply_smulCocycle, ha,
    smul_mul', smul_inv']
  group

/-- The **action of `A''ᴳ` on `H¹(G, A')`**: an element `c` fixed by `G`, lifted to `b ∈ A`, sends
the class of a cocycle `f` to the class of `g ↦ b * f g * (g • b)⁻¹`
(`TauCeti.NonabelianH1.IsGroupExtension.smul_mk_eq`). The class does not depend on the lift. -/
noncomputable def smul (c : FixedPoints.subgroup G A'') (x : NonabelianH1 G A') :
    NonabelianH1 G A' :=
  lift (fun f ↦ NonabelianH1.mk (hE.smulCocycle _ (hE.apply_liftFixed_mem c) f))
    (fun _ _ h ↦ hE.mk_smulCocycle_eq _ _ rfl (mk_eq_mk_iff.mpr (Cocycle.equiv_iff.mp h))) x

private theorem smul_mk {c : FixedPoints.subgroup G A''} {b : A} (hb : p b = c)
    (f : Cocycle G A') :
    hE.smul c (NonabelianH1.mk f) = NonabelianH1.mk (hE.smulCocycle b (hb ▸ c.property) f) := by
  rw [smul, lift_mk]
  exact hE.mk_smulCocycle_eq _ _ (by rw [apply_liftFixed, hb]) rfl

/-- The action of `c ∈ A''ᴳ` on the class of a cocycle `f`: for any lift `b` of `c` to `A`, the
result is the class of any cocycle `f'` with `f' g = b * f g * (g • b)⁻¹` in `A`. -/
theorem smul_mk_eq {c : FixedPoints.subgroup G A''} {b : A} (hb : p b = c) {f f' : Cocycle G A'}
    (hf' : ∀ g, i (f' g) = b * i (f g) * (g • b)⁻¹) :
    hE.smul c (NonabelianH1.mk f) = NonabelianH1.mk f' :=
  (hE.smul_mk hb f).trans <| congrArg NonabelianH1.mk <| Cocycle.ext fun g ↦
    hE.isEmbedding.injective <| by rw [apply_smulCocycle, hf']

/-- The identity of `A''ᴳ` acts trivially on `H¹(G, A')`. -/
@[simp]
protected theorem one_smul (x : NonabelianH1 G A') : hE.smul 1 x = x := by
  induction x using induction_on with | mk f =>
  exact hE.smul_mk_eq (b := 1) (by simp) fun g ↦ by simp

/-- The action of `A''ᴳ` on `H¹(G, A')` is compatible with multiplication. -/
protected theorem mul_smul (c c' : FixedPoints.subgroup G A'') (x : NonabelianH1 G A') :
    hE.smul (c * c') x = hE.smul c (hE.smul c' x) := by
  induction x using induction_on with | mk f =>
  rw [hE.smul_mk (hE.apply_liftFixed c'), hE.smul_mk (hE.apply_liftFixed c)]
  exact hE.smul_mk_eq (b := hE.liftFixed c * hE.liftFixed c')
    (f' := hE.smulCocycle _ (hE.apply_liftFixed_mem c)
      (hE.smulCocycle _ (hE.apply_liftFixed_mem c') f))
    (by simp [apply_liftFixed]) fun g ↦ by
      simp only [apply_smulCocycle, smul_mul', mul_inv_rev, mul_assoc]

/-- Acting by `c⁻¹` and then by `c` is the identity on `H¹(G, A')`. -/
@[simp]
protected theorem smul_inv_smul (c : FixedPoints.subgroup G A'') (x : NonabelianH1 G A') :
    hE.smul c (hE.smul c⁻¹ x) = x := by
  rw [← hE.mul_smul, mul_inv_cancel, hE.one_smul]

/-- Acting by `c` and then by `c⁻¹` is the identity on `H¹(G, A')`. -/
@[simp]
protected theorem inv_smul_smul (c : FixedPoints.subgroup G A'') (x : NonabelianH1 G A') :
    hE.smul c⁻¹ (hE.smul c x) = x := by
  rw [← hE.mul_smul, inv_mul_cancel, hE.one_smul]

/-- The action of `A''ᴳ` on `H¹(G, A')` by `TauCeti.NonabelianH1.IsGroupExtension.smul`, as a
`MulAction`. -/
@[reducible] noncomputable def mulAction :
    MulAction (FixedPoints.subgroup G A'') (NonabelianH1 G A') where
  smul := hE.smul
  one_smul := hE.one_smul
  mul_smul := hE.mul_smul

/-- The scalar action of `TauCeti.NonabelianH1.IsGroupExtension.mulAction` is
`TauCeti.NonabelianH1.IsGroupExtension.smul`. -/
@[simp]
theorem mulAction_smul_def (c : FixedPoints.subgroup G A'') (x : NonabelianH1 G A') :
    letI := hE.mulAction
    c • x = hE.smul c x :=
  (rfl)

/-- The **connecting map** `A''ᴳ → H¹(G, A')`: an element `c` fixed by `G`, lifted to `b ∈ A`, goes
to the class of the cocycle `g ↦ b⁻¹ * g • b`
(`TauCeti.NonabelianH1.IsGroupExtension.connecting_eq_mk`). It is the image of the base point
under `c⁻¹`. -/
noncomputable def connecting (c : FixedPoints.subgroup G A'') : NonabelianH1 G A' :=
  hE.smul c⁻¹ 1

/-- The connecting map sends `c` to the image of the base point under `c⁻¹`. -/
theorem connecting_eq_smul (c : FixedPoints.subgroup G A'') : hE.connecting c = hE.smul c⁻¹ 1 :=
  (rfl)

/-- The connecting map in terms of a lift: if `b ∈ A` lifts `c`, then `δ c` is the class of any
cocycle `f` of `A'` with `f g = b⁻¹ * g • b` in `A`. -/
theorem connecting_eq_mk {c : FixedPoints.subgroup G A''} {b : A} (hb : p b = c)
    {f : Cocycle G A'} (hf : ∀ g, i (f g) = b⁻¹ * g • b) : hE.connecting c = NonabelianH1.mk f :=
  hE.smul_mk_eq (b := b⁻¹) (by simp [hb]) fun g ↦ by simp [hf]

/-- The connecting map preserves the base point. -/
@[simp]
theorem connecting_one : hE.connecting 1 = 1 :=
  (hE.connecting_eq_mk (b := 1) (by simp) (f := 1) fun g ↦ by simp).trans mk_one

/-- **Exactness at `A''ᴳ`**: the connecting map sends `c` to the base point exactly when `c` lifts
to a fixed point of `A`. -/
theorem connecting_eq_one_iff {c : FixedPoints.subgroup G A''} :
    hE.connecting c = 1 ↔ ∃ a ∈ FixedPoints.subgroup G A, p a = c := by
  obtain ⟨b, hb⟩ := hE.surjective c
  have hmem : ∀ g : G, (1 : Cocycle G A).twist b g ∈ Set.range i := fun g ↦
    (hE.mulExact _).mp <| by simp [hE.map_smul_right, hb, c.property g]
  set f := ((1 : Cocycle G A).twist b).liftOfMemRange i hE.isEmbedding hE.compatible_left hmem
  have hf : ∀ g, i (f g) = b⁻¹ * g • b := fun g ↦ by simp [f]
  rw [hE.connecting_eq_mk hb hf, mk_eq_one_iff]
  constructor
  · -- If `f g = a⁻¹ * g • a`, then `b * a⁻¹` is a fixed point of `A` lifting `c`.
    rintro ⟨a, ha⟩
    refine ⟨b * (i a)⁻¹, fun g ↦ ?_, by simp [hb, hE.mulExact.apply_apply_eq_one]⟩
    have h := congrArg i (ha g)
    simp only [hf, _root_.map_mul, _root_.map_inv, hE.map_smul_left] at h
    have hgb : g • b = b * ((i a)⁻¹ * g • i a) := by
      rw [← h]
      group
    rw [smul_mul', smul_inv', hgb]
    group
  · -- A fixed lift `a` differs from `b` by an element of `A'`, which bounds `f`.
    rintro ⟨a, ha, hac⟩
    obtain ⟨x, hx⟩ := (hE.mulExact (a⁻¹ * b)).mp (by simp [hac, hb])
    refine ⟨x, fun g ↦ hE.isEmbedding.injective ?_⟩
    simp only [hf, _root_.map_mul, _root_.map_inv, hE.map_smul_left, hx, smul_mul', smul_inv',
      ha g]
    group

/-- **The fibres of the connecting map** are the orbits of `Aᴳ`, acting on `A''ᴳ` by left
multiplication through `p`. -/
theorem connecting_eq_connecting_iff {c c' : FixedPoints.subgroup G A''} :
    hE.connecting c = hE.connecting c' ↔ ∃ a ∈ FixedPoints.subgroup G A, p a * c' = c := by
  have key : hE.connecting (c * c'⁻¹) = hE.smul c' (hE.connecting c) := by
    rw [connecting_eq_smul, connecting_eq_smul, ← hE.mul_smul, mul_inv_rev, inv_inv]
  have hc' : hE.smul c' (hE.connecting c') = 1 := by
    rw [connecting_eq_smul, hE.smul_inv_smul]
  -- Acting by `c'` is injective, so `δ c = δ c'` exactly when `δ (c * c'⁻¹) = 1`.
  have hinj : hE.connecting c = hE.connecting c' ↔ hE.connecting (c * c'⁻¹) = 1 := by
    rw [key, ← hc']
    refine ⟨congrArg _, fun h ↦ ?_⟩
    simpa only [hE.inv_smul_smul] using congrArg (hE.smul c'⁻¹) h
  simp only [hinj, hE.connecting_eq_one_iff, Subgroup.coe_mul, Subgroup.coe_inv,
    eq_mul_inv_iff_mul_eq]

/-- **The fibres of `H¹(G, A') → H¹(G, A)` are the `A''ᴳ`-orbits**: two classes have the same image
in `H¹(G, A)` exactly when one is carried to the other by a fixed point of `A''`. -/
theorem map_eq_map_iff {x y : NonabelianH1 G A'} :
    map (ContinuousMonoidHom.id G) i hE.compatible_left x =
        map (ContinuousMonoidHom.id G) i hE.compatible_left y ↔
      ∃ c : FixedPoints.subgroup G A'', hE.smul c x = y := by
  induction x using induction_on with | mk f =>
  induction y using induction_on with | mk f' =>
  constructor
  · rintro h
    rw [map_mk, map_mk] at h
    obtain ⟨a, ha⟩ := mk_eq_mk_iff.mp h
    simp only [Cocycle.map_apply, ContinuousMonoidHom.id_toFun] at ha
    -- Applying `p` to `i (f' g) = a⁻¹ * i (f g) * g • a` shows that `p a` is fixed by `G`.
    have hfix : p a⁻¹ ∈ FixedPoints.subgroup G A'' := fun g ↦ by
      have h := congrArg p (ha g)
      simp only [_root_.map_mul, _root_.map_inv, hE.map_smul_right,
        hE.mulExact.apply_apply_eq_one, mul_one] at h
      rw [_root_.map_inv, smul_inv', inv_inj]
      exact (inv_mul_eq_one.mp h.symm).symm
    exact ⟨⟨p a⁻¹, hfix⟩, hE.smul_mk_eq rfl fun g ↦ by simp [ha]⟩
  · rintro ⟨c, hc⟩
    obtain ⟨b, hb⟩ := hE.surjective c
    obtain ⟨f'', hf''⟩ : ∃ f'' : Cocycle G A',
        hE.smul c (NonabelianH1.mk f) = NonabelianH1.mk f'' ∧
          ∀ g, i (f'' g) = b * i (f g) * (g • b)⁻¹ :=
      ⟨hE.smulCocycle b (hb ▸ c.property) f, hE.smul_mk hb f, hE.apply_smulCocycle _ _ f⟩
    rw [← hc, hf''.1, map_mk, map_mk]
    exact mk_eq_mk_iff.mpr ⟨b⁻¹, fun g ↦ by simp [hf''.2]⟩

/-- **Exactness at `H¹(G, A')`**: a class maps to the base point of `H¹(G, A)` exactly when it is
in the image of the connecting map. -/
theorem map_eq_one_iff_mem_range_connecting {x : NonabelianH1 G A'} :
    map (ContinuousMonoidHom.id G) i hE.compatible_left x = 1 ↔ x ∈ Set.range hE.connecting := by
  rw [← map_one (ContinuousMonoidHom.id G) i hE.compatible_left, hE.map_eq_map_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [connecting_eq_smul, ← hc, hE.inv_smul_smul]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [connecting_eq_smul, hE.smul_inv_smul]⟩

/-- **Exactness at `H¹(G, A)`**: a class maps to the base point of `H¹(G, A'')` exactly when it
comes from `H¹(G, A')`. -/
theorem map_eq_one_iff_mem_range_map {x : NonabelianH1 G A} :
    map (ContinuousMonoidHom.id G) p hE.compatible_right x = 1 ↔
      x ∈ Set.range (map (ContinuousMonoidHom.id G) i hE.compatible_left) := by
  constructor
  · induction x using induction_on with | mk f =>
    rw [map_mk, mk_eq_one_iff]
    -- If `p (f g) = a⁻¹ * g • a`, twisting `f` by the inverse of a lift `b` of `a` lands in `A'`.
    rintro ⟨a, ha⟩
    obtain ⟨b, rfl⟩ := hE.surjective a
    have hmem : ∀ g, f.twist b⁻¹ g ∈ Set.range i := fun g ↦ (hE.mulExact _).mp <| by
      have hpf : p (f g) = (p b)⁻¹ * g • p b := by
        simpa only [Cocycle.map_apply, ContinuousMonoidHom.id_toFun] using ha g
      simp only [Cocycle.twist_apply, inv_inv, _root_.map_mul, _root_.map_inv, hpf,
        hE.map_smul_right, smul_inv']
      group
    refine ⟨NonabelianH1.mk ((f.twist b⁻¹).liftOfMemRange i hE.isEmbedding hE.compatible_left
      hmem), ?_⟩
    rw [map_mk, Cocycle.map_liftOfMemRange, mk_twist]
  · rintro ⟨y, rfl⟩
    induction y using induction_on with | mk f' =>
    rw [map_mk, map_mk, mk_eq_one_iff]
    exact ⟨1, fun g ↦ by simp [hE.mulExact.apply_apply_eq_one]⟩

/-- **The neutral fibre of `H¹(G, A) → H¹(G, A'')`** is the quotient of `H¹(G, A')` by the action of
`A''ᴳ`: the map `H¹(G, A') → H¹(G, A)` induces a bijection from the `A''ᴳ`-orbits onto the classes
of `H¹(G, A)` mapping to the base point of `H¹(G, A'')`. -/
noncomputable def orbitRelQuotientEquiv :
    letI := hE.mulAction
    MulAction.orbitRel.Quotient (FixedPoints.subgroup G A'') (NonabelianH1 G A') ≃
      {x : NonabelianH1 G A // map (ContinuousMonoidHom.id G) p hE.compatible_right x = 1} :=
  letI := hE.mulAction
  Equiv.ofBijective
    (Quotient.lift
      (fun x ↦ ⟨map (ContinuousMonoidHom.id G) i hE.compatible_left x,
        hE.map_eq_one_iff_mem_range_map.mpr ⟨x, rfl⟩⟩)
      fun _ _ ⟨c, hc⟩ ↦ Subtype.ext (hE.map_eq_map_iff.mpr ⟨c, hc⟩).symm)
    ⟨fun x y h ↦ by
      induction x using Quotient.inductionOn
      induction y using Quotient.inductionOn
      obtain ⟨c, hc⟩ := hE.map_eq_map_iff.mp (congrArg Subtype.val h)
      exact Quotient.sound ⟨c⁻¹, by
        rw [← hc]
        exact hE.inv_smul_smul c _⟩,
    fun ⟨x, hx⟩ ↦ by
      obtain ⟨y, rfl⟩ := hE.map_eq_one_iff_mem_range_map.mp hx
      exact ⟨Quotient.mk _ y, rfl⟩⟩

/-- The orbit of a class goes to its image in `H¹(G, A)`. -/
@[simp]
theorem coe_orbitRelQuotientEquiv_mk (x : NonabelianH1 G A') :
    (hE.orbitRelQuotientEquiv (Quotient.mk _ x) : NonabelianH1 G A) =
      map (ContinuousMonoidHom.id G) i hE.compatible_left x :=
  (rfl)

end Action

end IsGroupExtension

end NonabelianH1

end TauCeti
