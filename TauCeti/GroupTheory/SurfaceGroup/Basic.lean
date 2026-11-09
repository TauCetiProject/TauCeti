/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.GroupTheory.PresentedGroup

/-!
# Surface groups with boundary

For natural numbers `g` and `m`, the orientable surface group `S⁺(g, m)` is the group presented by
generators `a₁, b₁, …, a_g, b_g, p₁, …, p_m` subject to the single relation

`[a₁, b₁] ⋯ [a_g, b_g] p₁ ⋯ p_m = 1`,

with the commutator convention `[x, y] = x⁻¹ * y⁻¹ * x * y`. The nonorientable surface group
`S⁻(g, m)` is presented by generators `c₁, …, c_g, p₁, …, p_m` subject to

`c₁ ^ 2 ⋯ c_g ^ 2 p₁ ⋯ p_m = 1`.

These are the fundamental groups of the compact surfaces of genus `g` with `m` boundary
components, orientable and nonorientable respectively. The generators `p_j` are the *peripheral*
elements: each is represented by a loop around one boundary component, and the cyclic subgroups
they generate, with their conjugates, are the boundary subgroups. Closed surfaces are the case
`m = 0`. The nonorientable presentation is meant for `g ≥ 1`; for `g = 0` it agrees with the
orientable one.

The presentations are taken as definitions. The word on the left of each defining relation is
available in an arbitrary group (`TauCeti.SurfaceGroup.orientableWord` and
`TauCeti.SurfaceGroup.nonorientableWord`), so that the universal properties read: homomorphisms
out of a surface group correspond to tuples of elements at which the surface word is trivial.

## Main definitions

* `TauCeti.SurfaceGroup.Orientable g m`: the orientable surface group `S⁺(g, m)`, with generators
  `TauCeti.SurfaceGroup.Orientable.a`, `TauCeti.SurfaceGroup.Orientable.b` and peripheral elements
  `TauCeti.SurfaceGroup.Orientable.peripheral`.
* `TauCeti.SurfaceGroup.Nonorientable g m`: the nonorientable surface group `S⁻(g, m)`, with
  generators `TauCeti.SurfaceGroup.Nonorientable.c` and peripheral elements
  `TauCeti.SurfaceGroup.Nonorientable.peripheral`.
* `TauCeti.SurfaceGroup.Orientable.lift` and `TauCeti.SurfaceGroup.Nonorientable.lift`: the
  universal properties, and `TauCeti.SurfaceGroup.Orientable.homEquiv` and
  `TauCeti.SurfaceGroup.Nonorientable.homEquiv`, the bijections between homomorphisms out of a
  surface group and the tuples satisfying its relation.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, Section 1.2 (the fundamental groups of the closed surfaces
  `M_g` and `N_g` from their polygon presentations).
* V. Guirardel, G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §5.1
  (fundamental groups of compact surfaces with their boundary subgroups).
-/

public section

namespace TauCeti

namespace SurfaceGroup

open FreeGroup (of)

variable {G H : Type*} [Group G] [Group H]

section Words

variable {g m : ℕ}

/-- The orientable surface word `[α₁, β₁] ⋯ [α_g, β_g] γ₁ ⋯ γ_m` in a group, with the commutator
convention `[x, y] = x⁻¹ * y⁻¹ * x * y`. Its vanishing is the defining relation of the orientable
surface group `S⁺(g, m)`. -/
def orientableWord (α β : Fin g → G) (γ : Fin m → G) : G :=
  (List.ofFn fun i ↦ (α i)⁻¹ * (β i)⁻¹ * α i * β i).prod * (List.ofFn γ).prod

theorem orientableWord_def (α β : Fin g → G) (γ : Fin m → G) :
    orientableWord α β γ =
      (List.ofFn fun i ↦ (α i)⁻¹ * (β i)⁻¹ * α i * β i).prod * (List.ofFn γ).prod := (rfl)

/-- A homomorphism carries the orientable surface word to the surface word of the images. -/
theorem map_orientableWord (f : G →* H) (α β : Fin g → G) (γ : Fin m → G) :
    f (orientableWord α β γ) =
      orientableWord (fun i ↦ f (α i)) (fun i ↦ f (β i)) fun j ↦ f (γ j) := by
  simp [orientableWord, map_list_prod, List.map_ofFn, Function.comp_def]

section Nonorientable

variable {M N : Type*} [Monoid M] [Monoid N]

/-- The nonorientable surface word `κ₁ ^ 2 ⋯ κ_g ^ 2 γ₁ ⋯ γ_m` in a monoid. Its vanishing is the
defining relation of the nonorientable surface group `S⁻(g, m)`. -/
def nonorientableWord (κ : Fin g → M) (γ : Fin m → M) : M :=
  (List.ofFn fun i ↦ κ i ^ 2).prod * (List.ofFn γ).prod

theorem nonorientableWord_def (κ : Fin g → M) (γ : Fin m → M) :
    nonorientableWord κ γ = (List.ofFn fun i ↦ κ i ^ 2).prod * (List.ofFn γ).prod := (rfl)

/-- A homomorphism carries the nonorientable surface word to the surface word of the images. -/
theorem map_nonorientableWord (f : M →* N) (κ : Fin g → M) (γ : Fin m → M) :
    f (nonorientableWord κ γ) = nonorientableWord (fun i ↦ f (κ i)) fun j ↦ f (γ j) := by
  simp [nonorientableWord, map_list_prod, List.map_ofFn, Function.comp_def]

end Nonorientable

end Words

/-- The generators `a₁, b₁, …, a_g, b_g, p₁, …, p_m` of the orientable surface group
`S⁺(g, m)`. -/
inductive OrientableGenerator (g m : ℕ) : Type
  /-- The generator `aᵢ`, the first curve of the `i`-th handle. -/
  | a (i : Fin g) : OrientableGenerator g m
  /-- The generator `bᵢ`, the second curve of the `i`-th handle. -/
  | b (i : Fin g) : OrientableGenerator g m
  /-- The peripheral generator `pⱼ`, a loop around the `j`-th boundary component. -/
  | peripheral (j : Fin m) : OrientableGenerator g m

/-- The generators `c₁, …, c_g, p₁, …, p_m` of the nonorientable surface group `S⁻(g, m)`. -/
inductive NonorientableGenerator (g m : ℕ) : Type
  /-- The generator `cᵢ`, the core of the `i`-th crosscap. -/
  | c (i : Fin g) : NonorientableGenerator g m
  /-- The peripheral generator `pⱼ`, a loop around the `j`-th boundary component. -/
  | peripheral (j : Fin m) : NonorientableGenerator g m

/-- The defining relator `[a₁, b₁] ⋯ [a_g, b_g] p₁ ⋯ p_m` of `S⁺(g, m)` in the free group on its
generators. -/
def orientableRelator (g m : ℕ) : FreeGroup (OrientableGenerator g m) :=
  orientableWord (fun i ↦ of (.a i)) (fun i ↦ of (.b i)) fun j ↦ of (.peripheral j)

/-- The defining relator `c₁ ^ 2 ⋯ c_g ^ 2 p₁ ⋯ p_m` of `S⁻(g, m)` in the free group on its
generators. -/
def nonorientableRelator (g m : ℕ) : FreeGroup (NonorientableGenerator g m) :=
  nonorientableWord (fun i ↦ of (.c i)) fun j ↦ of (.peripheral j)

/-- The orientable surface group
`S⁺(g, m) = ⟨a₁, b₁, …, a_g, b_g, p₁, …, p_m | [a₁, b₁] ⋯ [a_g, b_g] p₁ ⋯ p_m⟩`, the fundamental
group of the compact orientable surface of genus `g` with `m` boundary components. -/
abbrev Orientable (g m : ℕ) : Type := PresentedGroup {orientableRelator g m}

/-- The nonorientable surface group
`S⁻(g, m) = ⟨c₁, …, c_g, p₁, …, p_m | c₁ ^ 2 ⋯ c_g ^ 2 p₁ ⋯ p_m⟩`, for `g ≥ 1` the fundamental
group of the compact nonorientable surface of genus `g` with `m` boundary components. -/
abbrev Nonorientable (g m : ℕ) : Type := PresentedGroup {nonorientableRelator g m}

namespace Orientable

variable (g m : ℕ)

/-- The generator `aᵢ` of `S⁺(g, m)`. -/
def a (i : Fin g) : Orientable g m := PresentedGroup.of (.a i)

/-- The generator `bᵢ` of `S⁺(g, m)`. -/
def b (i : Fin g) : Orientable g m := PresentedGroup.of (.b i)

/-- The peripheral element `pⱼ` of `S⁺(g, m)`, a loop around the `j`-th boundary component. -/
def peripheral (j : Fin m) : Orientable g m := PresentedGroup.of (.peripheral j)

/-- The defining relation `[a₁, b₁] ⋯ [a_g, b_g] p₁ ⋯ p_m = 1` of `S⁺(g, m)`. -/
@[simp]
theorem orientableWord_a_b_peripheral : orientableWord (a g m) (b g m) (peripheral g m) = 1 :=
  (map_orientableWord (PresentedGroup.mk _) _ _ _).symm.trans <|
    PresentedGroup.one_of_mem (Set.mem_singleton _)

/-- In `S⁺(g, m + 1)` the last peripheral element is determined by the other generators:
`p_{m+1} = ([a₁, b₁] ⋯ [a_g, b_g] p₁ ⋯ p_m)⁻¹`. -/
theorem peripheral_last :
    peripheral g (m + 1) (Fin.last m) =
      ((List.ofFn fun i ↦
          (a g (m + 1) i)⁻¹ * (b g (m + 1) i)⁻¹ * a g (m + 1) i * b g (m + 1) i).prod *
        (List.ofFn fun j : Fin m ↦ peripheral g (m + 1) j.castSucc).prod)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  have h := orientableWord_a_b_peripheral g (m + 1)
  rwa [orientableWord, List.ofFn_succ', List.prod_concat, ← mul_assoc] at h

variable {g m}

/-- **The universal property of the orientable surface group.** Families `α β : Fin g → G` and
`γ : Fin m → G` whose surface word is trivial define a homomorphism out of `S⁺(g, m)` sending
`aᵢ, bᵢ, pⱼ` to `α i, β i, γ j`. -/
def lift (α β : Fin g → G) (γ : Fin m → G) (h : orientableWord α β γ = 1) :
    Orientable g m →* G :=
  PresentedGroup.toGroup
    (f := fun | .a i => α i | .b i => β i | .peripheral j => γ j) <| by
      rintro _ rfl
      rw [orientableRelator, map_orientableWord]
      simpa using h

@[simp]
theorem lift_a (α β : Fin g → G) (γ : Fin m → G) (h : orientableWord α β γ = 1) (i : Fin g) :
    lift α β γ h (a g m i) = α i :=
  PresentedGroup.toGroup.of _

@[simp]
theorem lift_b (α β : Fin g → G) (γ : Fin m → G) (h : orientableWord α β γ = 1) (i : Fin g) :
    lift α β γ h (b g m i) = β i :=
  PresentedGroup.toGroup.of _

@[simp]
theorem lift_peripheral (α β : Fin g → G) (γ : Fin m → G) (h : orientableWord α β γ = 1)
    (j : Fin m) : lift α β γ h (peripheral g m j) = γ j :=
  PresentedGroup.toGroup.of _

/-- A homomorphism out of `S⁺(g, m)` is determined by its values on the generators. -/
@[ext]
theorem hom_ext {f f' : Orientable g m →* G} (ha : ∀ i, f (a g m i) = f' (a g m i))
    (hb : ∀ i, f (b g m i) = f' (b g m i))
    (hp : ∀ j, f (peripheral g m j) = f' (peripheral g m j)) : f = f' :=
  PresentedGroup.ext fun
    | .a i => ha i
    | .b i => hb i
    | .peripheral j => hp j

/-- Homomorphisms `S⁺(g, m) →* G` correspond to the triples of families `(α, β, γ)` in `G` whose
surface word is trivial, by evaluation at the generators. -/
def homEquiv :
    (Orientable g m →* G) ≃
      {t : (Fin g → G) × (Fin g → G) × (Fin m → G) // orientableWord t.1 t.2.1 t.2.2 = 1} where
  toFun f := ⟨(fun i ↦ f (a g m i), fun i ↦ f (b g m i), fun j ↦ f (peripheral g m j)), by
    rw [← map_orientableWord, orientableWord_a_b_peripheral, map_one]⟩
  invFun t := lift t.1.1 t.1.2.1 t.1.2.2 t.2
  left_inv f := by ext <;> simp
  right_inv t := by ext <;> simp

@[simp]
theorem homEquiv_apply (f : Orientable g m →* G) :
    (homEquiv f : (Fin g → G) × (Fin g → G) × (Fin m → G)) =
      (fun i ↦ f (a g m i), fun i ↦ f (b g m i), fun j ↦ f (peripheral g m j)) := (rfl)

@[simp]
theorem homEquiv_symm_apply
    (t : {t : (Fin g → G) × (Fin g → G) × (Fin m → G) // orientableWord t.1 t.2.1 t.2.2 = 1}) :
    homEquiv.symm t = lift t.1.1 t.1.2.1 t.1.2.2 t.2 := (rfl)

end Orientable

namespace Nonorientable

variable (g m : ℕ)

/-- The generator `cᵢ` of `S⁻(g, m)`. -/
def c (i : Fin g) : Nonorientable g m := PresentedGroup.of (.c i)

/-- The peripheral element `pⱼ` of `S⁻(g, m)`, a loop around the `j`-th boundary component. -/
def peripheral (j : Fin m) : Nonorientable g m := PresentedGroup.of (.peripheral j)

/-- The defining relation `c₁ ^ 2 ⋯ c_g ^ 2 p₁ ⋯ p_m = 1` of `S⁻(g, m)`. -/
@[simp]
theorem nonorientableWord_c_peripheral : nonorientableWord (c g m) (peripheral g m) = 1 :=
  (map_nonorientableWord (PresentedGroup.mk _) _ _).symm.trans <|
    PresentedGroup.one_of_mem (Set.mem_singleton _)

/-- In `S⁻(g, m + 1)` the last peripheral element is determined by the other generators:
`p_{m+1} = (c₁ ^ 2 ⋯ c_g ^ 2 p₁ ⋯ p_m)⁻¹`. -/
theorem peripheral_last :
    peripheral g (m + 1) (Fin.last m) =
      ((List.ofFn fun i ↦ c g (m + 1) i ^ 2).prod *
        (List.ofFn fun j : Fin m ↦ peripheral g (m + 1) j.castSucc).prod)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  have h := nonorientableWord_c_peripheral g (m + 1)
  rwa [nonorientableWord, List.ofFn_succ', List.prod_concat, ← mul_assoc] at h

variable {g m}

/-- **The universal property of the nonorientable surface group.** Families `κ : Fin g → G` and
`γ : Fin m → G` whose surface word is trivial define a homomorphism out of `S⁻(g, m)` sending
`cᵢ, pⱼ` to `κ i, γ j`. -/
def lift (κ : Fin g → G) (γ : Fin m → G) (h : nonorientableWord κ γ = 1) :
    Nonorientable g m →* G :=
  PresentedGroup.toGroup (f := fun | .c i => κ i | .peripheral j => γ j) <| by
    rintro _ rfl
    rw [nonorientableRelator, map_nonorientableWord]
    simpa using h

@[simp]
theorem lift_c (κ : Fin g → G) (γ : Fin m → G) (h : nonorientableWord κ γ = 1) (i : Fin g) :
    lift κ γ h (c g m i) = κ i :=
  PresentedGroup.toGroup.of _

@[simp]
theorem lift_peripheral (κ : Fin g → G) (γ : Fin m → G) (h : nonorientableWord κ γ = 1)
    (j : Fin m) : lift κ γ h (peripheral g m j) = γ j :=
  PresentedGroup.toGroup.of _

/-- A homomorphism out of `S⁻(g, m)` is determined by its values on the generators. -/
@[ext]
theorem hom_ext {f f' : Nonorientable g m →* G} (hc : ∀ i, f (c g m i) = f' (c g m i))
    (hp : ∀ j, f (peripheral g m j) = f' (peripheral g m j)) : f = f' :=
  PresentedGroup.ext fun
    | .c i => hc i
    | .peripheral j => hp j

/-- Homomorphisms `S⁻(g, m) →* G` correspond to the pairs of families `(κ, γ)` in `G` whose
surface word is trivial, by evaluation at the generators. -/
def homEquiv :
    (Nonorientable g m →* G) ≃
      {t : (Fin g → G) × (Fin m → G) // nonorientableWord t.1 t.2 = 1} where
  toFun f := ⟨(fun i ↦ f (c g m i), fun j ↦ f (peripheral g m j)), by
    rw [← map_nonorientableWord, nonorientableWord_c_peripheral, map_one]⟩
  invFun t := lift t.1.1 t.1.2 t.2
  left_inv f := by ext <;> simp
  right_inv t := by ext <;> simp

@[simp]
theorem homEquiv_apply (f : Nonorientable g m →* G) :
    (homEquiv f : (Fin g → G) × (Fin m → G)) =
      (fun i ↦ f (c g m i), fun j ↦ f (peripheral g m j)) := (rfl)

@[simp]
theorem homEquiv_symm_apply
    (t : {t : (Fin g → G) × (Fin m → G) // nonorientableWord t.1 t.2 = 1}) :
    homEquiv.symm t = lift t.1.1 t.1.2 t.2 := (rfl)

end Nonorientable

end SurfaceGroup

end TauCeti
