/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.UniversalCentralExtension
import TauCeti.GroupTheory.Commutator

/-!
# Algebraic `K₂` of a ring

For an associative unital ring `R`, **algebraic `K₂(R)`** is the kernel of the canonical
homomorphism `St(R) →* GL_∞(R)` from the stable Steinberg group, sending each generator
`x_{ij}(a)` to the elementary matrix `e_{ij}(a)`. It records the relations among elementary
matrices which do not follow from the Steinberg relations. Together with the description of the
image as `E_∞(R)`, the kernel of `GL_∞(R) →* K₁(R)`, it fits into the exact sequence
`1 → K₂(R) → St(R) → GL_∞(R) → K₁(R) → 1`.

By the Kervaire–Steinberg theorem the kernel is central in `St(R)`, and since the centralizer
of `E_∞(R)` in `GL_∞(R)` is trivial, every central element of `St(R)` lies in the kernel: `K₂(R)`
is exactly the center of `St(R)`. In particular it is an abelian group. A ring homomorphism
`f : R →+* S` acts on the Steinberg generators by `x_{ij}(a) ↦ x_{ij}(f a)`, compatibly with its
action on `GL_∞`, and so induces a homomorphism `K₂(R) →* K₂(S)`, functorially.

For commuting units `u` and `v` of `R`, the diagonal matrices `diag(u, u⁻¹, 1)` and
`diag(v, 1, v⁻¹)` are stably elementary (by Whitehead's lemma), so they lift to `St(R)`. The
**Steinberg symbol** `{u, v}` is the commutator of any two such lifts: it does not depend on the
choice of lifts because two lifts of the same matrix differ by an element of the central
subgroup `K₂(R)`, and it lies in `K₂(R)` because the two diagonal matrices commute. For a field,
Matsumoto's theorem presents `K₂` by these symbols.

## Main definitions

* `TauCeti.algebraicK2`: the subgroup `K₂(R) = ker (St(R) →* GL_∞(R))` of `St(R)`.
* `TauCeti.algebraicK2.map`: the homomorphism `K₂(R) →* K₂(S)` induced by a ring homomorphism.
* `TauCeti.steinbergSymbol`: the Steinberg symbol `{u, v} ∈ K₂(R)` of commuting units.

## Main results

* `TauCeti.algebraicK2_eq_center`: `K₂(R)` is the center of the Steinberg group `St(R)`.
* `TauCeti.SteinbergGroup.range_toStableGL_eq_ker_of`: exactness of
  `St(R) → GL_∞(R) → K₁(R)` at `GL_∞(R)`.
* `TauCeti.algebraicK2.map_id`, `TauCeti.algebraicK2.map_comp`: functoriality of `K₂`.
* `TauCeti.coe_steinbergSymbol_eq_commutatorElement`: `{u, v}` is the commutator of any lifts of
  `diag(u, u⁻¹, 1)` and `diag(v, 1, v⁻¹)`.
* `TauCeti.algebraicK2.map_steinbergSymbol`: Steinberg symbols are natural in ring homomorphisms.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §5,
  the definition of `K₂` and Theorem 5.1 (`K₂` is the center of the Steinberg group), and §8
  (the symbols `{u, v}`).
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §5, Definition 5.2 (`K₂(R)` and its exact sequence),
  Theorem 5.2.1, and Definition 5.10 (Steinberg symbols).
-/

public section

noncomputable section

open Matrix

open scoped commutatorElement

namespace TauCeti

variable (R : Type*) [Ring R]

/-! ## The group `K₂(R)` -/

/-- **Algebraic `K₂`** of a ring `R`: the kernel of the canonical homomorphism
`St(R) →* GL_∞(R)` from the stable Steinberg group to the stable general linear group. -/
def algebraicK2 : Subgroup (SteinbergGroup R) :=
  (SteinbergGroup.toStableGL R).ker

variable {R}

/-- An element of the Steinberg group lies in `K₂` exactly when its image in `GL_∞` is trivial. -/
@[simp]
theorem mem_algebraicK2_iff {z : SteinbergGroup R} :
    z ∈ algebraicK2 R ↔ SteinbergGroup.toStableGL R z = 1 :=
  MonoidHom.mem_ker

/-- **`K₂(R)` is the center of the Steinberg group `St(R)`.** The kernel of `St(R) →* GL_∞(R)` is
central by the Kervaire–Steinberg theorem; conversely a central element of `St(R)` maps to an
element of `GL_∞(R)` commuting with the image `E_∞(R)`, whose centralizer is trivial. -/
theorem algebraicK2_eq_center : algebraicK2 R = Subgroup.center (SteinbergGroup R) := by
  refine le_antisymm SteinbergGroup.ker_toStableGL_le_center fun z hz ↦ ?_
  rw [mem_algebraicK2_iff, ← Subgroup.mem_bot,
    ← StableGeneralLinearGroup.centralizer_elementarySubgroup, ← SteinbergGroup.range_toStableGL,
    Subgroup.mem_centralizer_iff]
  rintro _ ⟨w, rfl⟩
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz w]

/-- `K₂(R)` is a commutative group. -/
instance : IsMulCommutative (algebraicK2 R) :=
  ⟨⟨fun a b ↦ Subtype.ext (Subgroup.mem_center_iff.1 (algebraicK2_eq_center.le b.property) a)⟩⟩

instance : (algebraicK2 R).Normal :=
  Subgroup.normal_of_le_center algebraicK2_eq_center.le

/-! ## The exact sequence `1 → K₂(R) → St(R) → GL_∞(R) → K₁(R) → 1` -/

/-- **Exactness of `St(R) → GL_∞(R) → K₁(R)` at `GL_∞(R)`**: the image of the Steinberg group in
`GL_∞(R)` is the kernel of the projection to algebraic `K₁`. Exactness at `K₂(R)` and `St(R)` is
the definition of `K₂(R)` as a kernel, and exactness at `K₁(R)` is the surjectivity of the
projection onto the abelianization. -/
theorem SteinbergGroup.range_toStableGL_eq_ker_of :
    (toStableGL R).range =
      (Group.Abelianization.of : StableGeneralLinearGroup R →* AlgebraicK1 R).ker := by
  rw [range_toStableGL, AlgebraicK1.ker_of]

/-! ## Functoriality -/

namespace algebraicK2

variable {S T : Type*} [Ring S] [Ring T]

/-- The homomorphism `K₂(R) →* K₂(S)` induced by a ring homomorphism `f : R →+* S`: the
restriction of the homomorphism of Steinberg groups `x_{ij}(a) ↦ x_{ij}(f a)`. -/
def map (f : R →+* S) : algebraicK2 R →* algebraicK2 S :=
  ((IndexedSteinbergGroup.map f).comp (algebraicK2 R).subtype).codRestrict _ fun z ↦ by
    simp [mem_algebraicK2_iff.1 z.property]

/-- The induced homomorphism of `K₂` is the induced homomorphism of Steinberg groups. -/
@[simp]
theorem coe_map_apply (f : R →+* S) (z : algebraicK2 R) :
    (map f z : SteinbergGroup S) = IndexedSteinbergGroup.map f (z : SteinbergGroup R) :=
  (rfl)

/-- The identity ring homomorphism induces the identity of `K₂`. -/
@[simp]
theorem map_id : map (RingHom.id R) = MonoidHom.id (algebraicK2 R) := by
  ext z
  simp

/-- Algebraic `K₂` is functorial. -/
theorem map_comp (f : R →+* S) (g : S →+* T) :
    map (g.comp f) = (map g).comp (map f) := by
  ext z
  simp

/-- Applying the homomorphisms of `K₂` induced by `f` and then `g` is applying the one induced
by `g.comp f`. -/
@[simp]
theorem map_map (f : R →+* S) (g : S →+* T) (z : algebraicK2 R) :
    map g (map f z) = map (g.comp f) z := by
  rw [map_comp, MonoidHom.comp_apply]

end algebraicK2

/-! ## Steinberg symbols -/

section Symbol

/-- The invertible diagonal matrix `diag(u, u⁻¹, 1)` is elementary. It is the stabilization of
Whitehead's matrix `u ⊕ u⁻¹`. -/
theorem diagGL_inv_one_mem_elementarySubgroup (u : Rˣ) :
    diagGL ![u, u⁻¹, 1] ∈ elementarySubgroup (Fin 3) R := by
  let w : GL (Fin 1) R := GeneralLinearGroup.scalar (Fin 1) u
  have hw : finSumFinEquiv.reindexGL R (fromBlocksGL (w, w⁻¹)) ∈ elementarySubgroup (Fin 2) R :=
    (Equiv.reindexGL_mem_elementarySubgroup_iff _).2 (fromBlocksGL_inv_mem_elementarySubgroup w)
  have h : stabilizeGL R (by norm_num : 2 ≤ 3)
      (finSumFinEquiv.reindexGL R (fromBlocksGL (w, w⁻¹))) = diagGL ![u, u⁻¹, 1] := by
    have h0 : finSumFinEquiv.symm (0 : Fin (1 + 1)) = Sum.inl 0 := by decide
    have h1 : finSumFinEquiv.symm (1 : Fin (1 + 1)) = Sum.inr 0 := by decide
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_stabilizeGL_apply, w, ← map_inv, h0, h1]
  exact h ▸ map_stabilizeGL_elementarySubgroup_le _ ⟨_, hw, rfl⟩

/-- The invertible diagonal matrix `diag(u, 1, u⁻¹)` is elementary. It is obtained from
`diag(u, u⁻¹, 1)` by exchanging the last two indices. -/
theorem diagGL_one_inv_mem_elementarySubgroup (u : Rˣ) :
    diagGL ![u, 1, u⁻¹] ∈ elementarySubgroup (Fin 3) R := by
  have h : (Equiv.swap (1 : Fin 3) 2).reindexGL R (diagGL ![u, u⁻¹, 1]) = diagGL ![u, 1, u⁻¹] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Equiv.swap_apply_of_ne_of_ne]
  exact h ▸ (Equiv.reindexGL_mem_elementarySubgroup_iff _).2
    (diagGL_inv_one_mem_elementarySubgroup u)

/-- For commuting units `u` and `v`, the commutator of `diag(u, u⁻¹, 1)` and `diag(v, 1, v⁻¹)`
is trivial. -/
private theorem commutatorElement_diagGL_eq_one {u v : Rˣ} (h : Commute u v) :
    ⁅diagGL ![u, u⁻¹, 1], diagGL ![v, 1, v⁻¹]⁆ = 1 := by
  rw [← map_commutatorElement, ← map_one diagGL]
  congr 1
  ext i : 1
  fin_cases i <;> simp [commutatorElement_def, h.eq]

/-- An elementary matrix, placed in `GL_∞(R)`, lifts to the Steinberg group `St(R)`. -/
private theorem exists_toStableGL_eq_of {n : ℕ} {g : GL (Fin n) R}
    (hg : g ∈ elementarySubgroup (Fin n) R) :
    ∃ a, SteinbergGroup.toStableGL R a = StableGeneralLinearGroup.of R n g :=
  MonoidHom.mem_range.1
    (SteinbergGroup.range_toStableGL.ge (StableGeneralLinearGroup.of_mem_elementarySubgroup hg))

/-- Two elements of `St(R)` with the same image in `GL_∞(R)` differ by a central element. -/
private theorem exists_mem_center_eq_mul {a a' : SteinbergGroup R}
    (h : SteinbergGroup.toStableGL R a = SteinbergGroup.toStableGL R a') :
    ∃ c ∈ Subgroup.center (SteinbergGroup R), a' = a * c := by
  refine ⟨a⁻¹ * a', algebraicK2_eq_center.le ?_, by group⟩
  rw [mem_algebraicK2_iff, map_mul, map_inv, h, inv_mul_cancel]

/-- The **Steinberg symbol** `{u, v} ∈ K₂(R)` of commuting units `u` and `v` of `R`: the
commutator `⁅a, b⁆` of lifts `a` and `b` to the Steinberg group `St(R)` of the stable matrices
`diag(u, u⁻¹, 1)` and `diag(v, 1, v⁻¹)`. It does not depend on the choice of lifts
(`TauCeti.coe_steinbergSymbol_eq_commutatorElement`). -/
def steinbergSymbol (u v : Rˣ) (h : Commute u v) : algebraicK2 R :=
  ⟨⁅(exists_toStableGL_eq_of (diagGL_inv_one_mem_elementarySubgroup u)).choose,
      (exists_toStableGL_eq_of (diagGL_one_inv_mem_elementarySubgroup v)).choose⁆, by
    rw [mem_algebraicK2_iff, map_commutatorElement,
      (exists_toStableGL_eq_of (diagGL_inv_one_mem_elementarySubgroup u)).choose_spec,
      (exists_toStableGL_eq_of (diagGL_one_inv_mem_elementarySubgroup v)).choose_spec,
      ← map_commutatorElement, commutatorElement_diagGL_eq_one h, map_one]⟩

/-- **The Steinberg symbol is independent of the lifts**: for any lifts `a` and `b` to `St(R)` of
`diag(u, u⁻¹, 1)` and `diag(v, 1, v⁻¹)`, the symbol `{u, v}` is the commutator `⁅a, b⁆`. -/
theorem coe_steinbergSymbol_eq_commutatorElement {u v : Rˣ} (h : Commute u v)
    {a b : SteinbergGroup R}
    (ha : SteinbergGroup.toStableGL R a = StableGeneralLinearGroup.of R 3 (diagGL ![u, u⁻¹, 1]))
    (hb : SteinbergGroup.toStableGL R b = StableGeneralLinearGroup.of R 3 (diagGL ![v, 1, v⁻¹])) :
    (steinbergSymbol u v h : SteinbergGroup R) = ⁅a, b⁆ := by
  obtain ⟨c, hc, rfl⟩ := exists_mem_center_eq_mul
    ((exists_toStableGL_eq_of (diagGL_inv_one_mem_elementarySubgroup u)).choose_spec.trans ha.symm)
  obtain ⟨d, hd, rfl⟩ := exists_mem_center_eq_mul
    ((exists_toStableGL_eq_of (diagGL_one_inv_mem_elementarySubgroup v)).choose_spec.trans hb.symm)
  exact (commutatorElement_mul_mul_of_mem_center hc hd).symm

/-- The Steinberg symbol `{1, v}` is trivial. -/
@[simp]
theorem steinbergSymbol_one_left (v : Rˣ) : steinbergSymbol 1 v (Commute.one_left v) = 1 := by
  obtain ⟨b, hb⟩ := exists_toStableGL_eq_of (diagGL_one_inv_mem_elementarySubgroup v)
  refine Subtype.ext ((coe_steinbergSymbol_eq_commutatorElement _ (a := 1) ?_ hb).trans ?_)
  · rw [map_one, ← map_one (StableGeneralLinearGroup.of R 3), ← map_one diagGL]
    congr 2
    ext i : 1
    fin_cases i <;> simp
  · simp [commutatorElement_def]

/-- The Steinberg symbol `{u, 1}` is trivial. -/
@[simp]
theorem steinbergSymbol_one_right (u : Rˣ) : steinbergSymbol u 1 (Commute.one_right u) = 1 := by
  obtain ⟨a, ha⟩ := exists_toStableGL_eq_of (diagGL_inv_one_mem_elementarySubgroup u)
  refine Subtype.ext ((coe_steinbergSymbol_eq_commutatorElement _ ha (b := 1) ?_).trans ?_)
  · rw [map_one, ← map_one (StableGeneralLinearGroup.of R 3), ← map_one diagGL]
    congr 2
    ext i : 1
    fin_cases i <;> simp
  · simp [commutatorElement_def]

/-- **Steinberg symbols are natural**: the homomorphism of `K₂` induced by a ring homomorphism
`f` sends `{u, v}` to `{f u, f v}`. -/
@[simp]
theorem algebraicK2.map_steinbergSymbol {S : Type*} [Ring S] (f : R →+* S) {u v : Rˣ}
    (h : Commute u v) :
    algebraicK2.map f (steinbergSymbol u v h) =
      steinbergSymbol (Units.map (f : R →* S) u) (Units.map (f : R →* S) v) (h.map _) := by
  obtain ⟨a, ha⟩ := exists_toStableGL_eq_of (diagGL_inv_one_mem_elementarySubgroup u)
  obtain ⟨b, hb⟩ := exists_toStableGL_eq_of (diagGL_one_inv_mem_elementarySubgroup v)
  have hdiag (d : Fin 3 → Rˣ) :
      StableGeneralLinearGroup.map f (StableGeneralLinearGroup.of R 3 (diagGL d)) =
        StableGeneralLinearGroup.of S 3 (diagGL fun i ↦ Units.map (f : R →* S) (d i)) := by
    rw [StableGeneralLinearGroup.map_of]
    congr 1
    ext i j
    simp [diagonal_apply, apply_ite f]
  refine Subtype.ext ?_
  rw [algebraicK2.coe_map_apply, coe_steinbergSymbol_eq_commutatorElement h ha hb,
    map_commutatorElement]
  refine (coe_steinbergSymbol_eq_commutatorElement _ ?_ ?_).symm
  · rw [SteinbergGroup.toStableGL_map, ha, hdiag]
    congr 2
    ext i : 1
    fin_cases i <;> simp
  · rw [SteinbergGroup.toStableGL_map, hb, hdiag]
    congr 2
    ext i : 1
    fin_cases i <;> simp

end Symbol

end TauCeti
