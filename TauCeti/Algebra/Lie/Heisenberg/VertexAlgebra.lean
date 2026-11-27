/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Heisenberg.Fock
public import TauCeti.Algebra.Vertex.Reconstruction
public import TauCeti.Algebra.Vertex.Subalgebra

/-!
# The Heisenberg vertex algebra

Let `H` be a module over a commutative ring `R` with a symmetric bilinear form `B`, and let
`π = Sym(⊕_{n > 0} H t⁻ⁿ)` be the Fock module of the Heisenberg algebra of `H`
(`TauCeti.HeisenbergFockSpace`), with vacuum `|0⟩ = 1`, mode operators `h(n)` and translation
operator `T`. The **free boson field** of `h : H` is

`h(z) = ∑ₙ h(n) z^{-n-1}`

(`TauCeti.HeisenbergFockSpace.bosonField`), a field on `π` because every state is killed by all
sufficiently high modes. The free boson fields are

* translation covariant, `[T, h(z)] = ∂_z h(z)`, which is `[T, h(n)] = -n h(n-1)`
  (`TauCeti.HeisenbergFockSpace.lie_translation_ncoeff_bosonField`);
* mutually local of order `2`, since `[h(z), k(w)] = B(h, k) ∂_w δ(z - w)` is killed by
  `(z - w)²` (`TauCeti.HeisenbergFockSpace.isLocalOfOrder_bosonField`);
* generating: the negative modes `h(-(j+1))` build `π` from the vacuum.

So when `π` has unique divisibility, for instance over a `ℚ`-algebra, the reconstruction theorem
`TauCeti.existsUnique_formalVertexAxioms` gives a unique formal vertex algebra on `π` with vacuum
`1`, translation `T` and

`Y(h(-1)|0⟩, z) = h(z)`

(`TauCeti.HeisenbergFockSpace.formalVertexAxioms`). This is the **Heisenberg vertex algebra**
(the free boson, or the uncharged Fock vertex algebra) of `(H, B)`. Its fields are iterated `n`-th
products of free boson fields, `Y(h(n) b, z) = h(z)₍ₙ₎ Y(b, z)`, and the products of the generating
states `h(-1)|0⟩` are the operator product expansion

`h(z) k(w) ∼ B(h, k) / (z - w)²`

(`TauCeti.HeisenbergFockSpace.ncoeff_natCast_bosonField_ι_single_zero`):
`h₍₁₎ k(-1)|0⟩ = B(h, k)|0⟩` and `h₍ₙ₎ k(-1)|0⟩ = 0` for the other `n ≥ 0`. The form `B` may be
degenerate, including zero, when every nonnegative product of generating states vanishes.

The construction is functorial for isometries. An isometry `f : (H, B) → (H', B')`
(`LinearMap.BilinForm.Isometry`, written `B →bᵢ B'`) induces the algebra map `π(H) → π(H')` of
symmetric algebras (`SymmetricAlgebra.map`), which preserves the vacuum and intertwines the modes,
`f(h(n) p) = (f h)(n) f(p)` (`TauCeti.HeisenbergFockSpace.map_modeOperator`, in the Fock module
file). Since the states
`h(-1)|0⟩` generate the Heisenberg vertex algebra
(`TauCeti.HeisenbergFockSpace.adjoin_range_ι_single_zero_eq_top`), it is a morphism of formal
vertex algebras (`TauCeti.HeisenbergFockSpace.formalVertexAxiomsHom`).

## Main definitions

* `TauCeti.HeisenbergFockSpace.bosonField`: the free boson field `h(z)`.
* `TauCeti.HeisenbergFockSpace.formalVertexAxioms`: the Heisenberg vertex algebra.
* `TauCeti.HeisenbergFockSpace.formalVertexAxiomsHom`: the morphism of Heisenberg vertex algebras
  induced by an isometry.

## Main results

* `TauCeti.HeisenbergFockSpace.isLocalOfOrder_bosonField`: free boson fields are mutually local of
  order `2`.
* `TauCeti.HeisenbergFockSpace.formalVertexAxioms_field_ι_single_zero`: `Y(h(-1)|0⟩, z) = h(z)`.
* `TauCeti.HeisenbergFockSpace.formalVertexAxioms_field_modeOperator_apply`:
  `Y(h(n) b, z) = h(z)₍ₙ₎ Y(b, z)`.
* `TauCeti.HeisenbergFockSpace.eq_formalVertexAxioms`: uniqueness of the Heisenberg vertex
  algebra.
* `TauCeti.HeisenbergFockSpace.ncoeff_natCast_bosonField_ι_single_zero`: the operator product
  expansion of two free boson fields.
* `TauCeti.HeisenbergFockSpace.adjoin_range_ι_single_zero_eq_top`: the states `h(-1)|0⟩` generate
  the Heisenberg vertex algebra.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, Cambridge University Press (2007),
  §6.2.1, for the Fock vertex algebra of the Heisenberg Lie algebra.
* E. Frenkel and D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., American
  Mathematical Society (2004), §2.3, for the free boson as an application of the reconstruction
  theorem.
* V. G. Kac, *Vertex Algebras for Beginners*, 2nd ed., American Mathematical Society (1998), §3.5
  and Theorem 4.5, for the free boson and its vertex algebra structure.
-/

public section

noncomputable section

open scoped VertexOperator
open SymmetricAlgebra VertexOperator

namespace TauCeti

namespace HeisenbergFockSpace

variable {R H : Type*} [CommRing R] [AddCommGroup H] [Module R H] (B : LinearMap.BilinForm R H)

/-! ### Free boson fields -/

/-- The coefficients `z^k ↦ h(-k-1)` of a free boson field have support bounded below at each
state. -/
private theorem bddBelow_support_modeOperator (h : H) (p : HeisenbergFockSpace R H) :
    BddBelow (Function.support fun k : ℤ ↦ modeOperator B (-k - 1) h p) := by
  obtain ⟨N, hN⟩ := exists_forall_modeOperator_eq_zero B p
  refine ⟨-(N : ℤ) - 1, fun k hk ↦ ?_⟩
  by_contra! hlt
  exact hk (hN _ (by omega) h)

/-- The **free boson field** `h(z) = ∑ₙ h(n) z^{-n-1}` of `h : H` on the Fock space. Its
normalized coefficients are the mode operators, `h(z)₍ₙ₎ = h(n)`
(`TauCeti.HeisenbergFockSpace.ncoeff_bosonField`). -/
def bosonField : H →ₗ[R] VertexOperator R (HeisenbergFockSpace R H) where
  toFun h := VertexOperator.of_coeff (fun k ↦ modeOperator B (-k - 1) h)
    (bddBelow_support_modeOperator B h)
  map_add' h k := VertexOperator.ext_ncoeff fun n ↦ by simp
  map_smul' r h := VertexOperator.ext_ncoeff fun n ↦ by simp

/-- The normalized coefficients of the free boson field of `h` are the mode operators `h(n)`. -/
@[simp]
theorem ncoeff_bosonField (h : H) (n : ℤ) : (bosonField B h)[[n]] = modeOperator B n h := by
  simp [bosonField]

/-- The free boson field applied to the vacuum at `z = 0` is the generating state:
`h(-1)|0⟩ = ι (single 0 h)`. -/
theorem ncoeff_neg_one_bosonField_one (h : H) :
    ((bosonField B h)[[-1]]) 1 = ι R (ℕ →₀ H) (Finsupp.single 0 h) := by
  simpa using modeOperator_neg_natCast_sub_one_apply B 0 h 1

/-- **Translation covariance.** `[T, h(z)] = ∂_z h(z)`, that is `[T, h(n)] = -n h(n-1)`. -/
theorem lie_translation_ncoeff_bosonField (h : H) (n : ℤ) :
    ⁅(translation (R := R) (H := H) : Module.End R (HeisenbergFockSpace R H)),
        (bosonField B h)[[n]]⁆ =
      (derivative (bosonField B h))[[n]] := by
  rw [Ring.lie_def, ncoeff_derivative, ncoeff_bosonField, ncoeff_bosonField, translation_commutator]
  simp [Int.cast_smul_eq_zsmul]

/-- **Locality.** For a symmetric form `B`, any two free boson fields are mutually local of
order `2`: `(z - w)² [h(z), k(w)] = 0`. -/
theorem isLocalOfOrder_bosonField (hB : B.IsSymm) (h k : H) :
    (bosonField B h).IsLocalOfOrder (bosonField B k) 2 := by
  refine isLocalOfOrder_iff.2 fun m n ↦ ?_
  -- All three index pairs `(m + i, n + j)` with `i + j = 2` have the same sum `m + n + 2`.
  have hmn (i j : ℕ) (h : i + j = 2) : m + i + (n + j) = m + n + 2 := by omega
  simp only [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    Finset.sum_singleton, ncoeff_bosonField, modeOperator_commutator B hB, hmn]
  split_ifs
  · -- The central terms `m - 2 (m + 1) + (m + 2)` cancel.
    simp only [Nat.choose_zero_right, Nat.choose_self, show Nat.choose 2 1 = 2 from rfl]
    push_cast
    module
  · simp

/-- **The operator product expansion** `h(z) k(w) ∼ B(h, k) / (z - w)²`: for `n ≥ 0`, the mode
`h(n)` sends the generating state `k(-1)|0⟩` to `B(h, k)|0⟩` for `n = 1` and to zero otherwise. In
the Heisenberg vertex algebra this is the `n`-th product of `h(-1)|0⟩` and `k(-1)|0⟩`. -/
theorem ncoeff_natCast_bosonField_ι_single_zero (h k : H) (n : ℕ) :
    ((bosonField B h)[[(n : ℤ)]]) (ι R (ℕ →₀ H) (Finsupp.single 0 k)) =
      if n = 1 then algebraMap R (HeisenbergFockSpace R H) (B h k) else 0 := by
  rcases n with _ | j
  · simp
  · rw [ncoeff_bosonField, Nat.cast_succ, modeOperator_natCast_add_one_apply, annihilation_ι_single]
    rcases j with _ | j <;> simp

/-! ### The Heisenberg vertex algebra -/

section VertexAlgebra

variable [HasUniqueDiv (HeisenbergFockSpace R H)] (hB : B.IsSymm)

/-- The **Heisenberg vertex algebra** of a symmetric bilinear space `(H, B)`: the formal vertex
algebra on the Fock space reconstructed from the free boson fields, with vacuum `1`, translation
`T` and `Y(h(-1)|0⟩, z) = h(z)`. It exists when the Fock space has unique divisibility, for
instance over a `ℚ`-algebra. -/
def formalVertexAxioms : FormalVertexAxioms R (HeisenbergFockSpace R H) :=
  FormalVertexAxioms.ofGeneratingFields (F := bosonField B) (vac := 1)
    (T := (translation (R := R) (H := H) : Module.End R (HeisenbergFockSpace R H)))
    translation.map_one_eq_zero
    (lie_translation_ncoeff_bosonField B) (fun h k ↦ ⟨2, isLocalOfOrder_bosonField B hB h k⟩)
    (fun W h1 hW ↦ eq_top_of_one_mem B W h1 fun n _ h p hp ↦ by simpa using hW h n p hp)

/-- The vacuum of the Heisenberg vertex algebra is `1`. -/
@[simp]
theorem formalVertexAxioms_vacuum : (formalVertexAxioms B hB).vacuum = 1 :=
  FormalVertexAxioms.ofGeneratingFields_vacuum ..

/-- The translation operator of the Heisenberg vertex algebra is `T`. -/
@[simp]
theorem formalVertexAxioms_translation :
    (formalVertexAxioms B hB).translation =
      (translation (R := R) (H := H) : Module.End R (HeisenbergFockSpace R H)) :=
  FormalVertexAxioms.ofGeneratingFields_translation ..

/-- The field of the generating state `h(-1)|0⟩` is the free boson field: `Y(h(-1)|0⟩, z) = h(z)`.
-/
@[simp]
theorem formalVertexAxioms_field_ι_single_zero (h : H) :
    (formalVertexAxioms B hB).field (ι R (ℕ →₀ H) (Finsupp.single 0 h)) = bosonField B h := by
  rw [← ncoeff_neg_one_bosonField_one]
  exact FormalVertexAxioms.ofGeneratingFields_field_ncoeff_neg_one_apply_vacuum ..

/-- The fields of the Heisenberg vertex algebra are iterated products of free boson fields:
`Y(h(n) b, z) = h(z)₍ₙ₎ Y(b, z)`. -/
theorem formalVertexAxioms_field_modeOperator_apply (h : H) (n : ℤ)
    (b : HeisenbergFockSpace R H) :
    (formalVertexAxioms B hB).field (modeOperator B n h b) =
      nthProduct n (bosonField B h) ((formalVertexAxioms B hB).field b) := by
  rw [← ncoeff_bosonField]
  exact FormalVertexAxioms.ofGeneratingFields_field_ncoeff_apply ..

variable {B hB} in
/-- **Uniqueness of the Heisenberg vertex algebra.** A formal vertex algebra on the Fock space with
vacuum `1`, translation `T` and `Y(h(-1)|0⟩, z) = h(z)` for every `h` is `formalVertexAxioms`. -/
theorem eq_formalVertexAxioms {A : FormalVertexAxioms R (HeisenbergFockSpace R H)}
    (hvac : A.vacuum = 1)
    (htr : A.translation = (translation (R := R) (H := H) : Module.End R (HeisenbergFockSpace R H)))
    (hfield : ∀ h : H, A.field (ι R (ℕ →₀ H) (Finsupp.single 0 h)) = bosonField B h) :
    A = formalVertexAxioms B hB :=
  FormalVertexAxioms.eq_ofGeneratingFields _ _ _ _ hvac htr fun h ↦ by
    rw [ncoeff_neg_one_bosonField_one, hfield]

/-- The generating states `h(-1)|0⟩` generate the Heisenberg vertex algebra. -/
theorem adjoin_range_ι_single_zero_eq_top :
    FormalVertexAxioms.VertexSubalgebra.adjoin (formalVertexAxioms B hB)
      (Set.range fun h : H ↦ ι R (ℕ →₀ H) (Finsupp.single 0 h)) = ⊤ := by
  set S := FormalVertexAxioms.VertexSubalgebra.adjoin (formalVertexAxioms B hB)
    (Set.range fun h : H ↦ ι R (ℕ →₀ H) (Finsupp.single 0 h))
  have hS : S.toSubmodule = ⊤ := by
    refine eq_top_of_one_mem B S.toSubmodule ?_ fun n _ h p hp ↦ ?_
    · simpa using S.vacuum_mem
    · have hh : ι R (ℕ →₀ H) (Finsupp.single 0 h) ∈ S :=
        FormalVertexAxioms.VertexSubalgebra.subset_adjoin _ ⟨h, rfl⟩
      simpa using S.ncoeff_field_apply_mem n hh hp
  exact (FormalVertexAxioms.VertexSubalgebra.eq_top_iff' S).2 fun v ↦
    FormalVertexAxioms.VertexSubalgebra.mem_toSubmodule.1 (hS ▸ Submodule.mem_top)

end VertexAlgebra

/-! ### Functoriality for isometries -/

section Map

variable {H' : Type*} [AddCommGroup H'] [Module R H'] (B' : LinearMap.BilinForm R H')

variable [HasUniqueDiv (HeisenbergFockSpace R H)] [HasUniqueDiv (HeisenbergFockSpace R H')]
  (hB : B.IsSymm) (hB' : B'.IsSymm)

/-- The morphism of Heisenberg vertex algebras induced by an isometry `f : (H, B) → (H', B')`:
the map of Fock spaces sending `h(-(j+1))|0⟩` to `(f h)(-(j+1))|0⟩`. -/
def formalVertexAxiomsHom (f : B →bᵢ B') :
    (formalVertexAxioms B hB).Hom (formalVertexAxioms B' hB') :=
  FormalVertexAxioms.Hom.ofAdjoinEqTop
    (SymmetricAlgebra.map R (Finsupp.mapRange.linearMap f.toLinearMap)).toLinearMap
    (adjoin_range_ι_single_zero_eq_top B hB) (by simp) (by
      rintro _ ⟨h, rfl⟩ n b
      simp [map_modeOperator f])

/-- The morphism induced by an isometry is the induced map of symmetric algebras. -/
@[simp]
theorem coe_formalVertexAxiomsHom (f : B →bᵢ B') :
    ⇑(formalVertexAxiomsHom B B' hB hB' f) =
      SymmetricAlgebra.map R (Finsupp.mapRange.linearMap f.toLinearMap) :=
  FormalVertexAxioms.Hom.coe_ofAdjoinEqTop ..

/-- The identity isometry induces the identity morphism. -/
@[simp]
theorem formalVertexAxiomsHom_id :
    formalVertexAxiomsHom B B hB hB (.id B) = FormalVertexAxioms.Hom.id (formalVertexAxioms B hB) :=
  FormalVertexAxioms.Hom.ext fun p ↦ by simp [LinearMap.BilinForm.Isometry.id]

/-- Composites of isometries induce composites of morphisms. -/
theorem formalVertexAxiomsHom_comp {H'' : Type*} [AddCommGroup H''] [Module R H'']
    (B'' : LinearMap.BilinForm R H'') [HasUniqueDiv (HeisenbergFockSpace R H'')]
    (hB'' : B''.IsSymm) (f : B →bᵢ B') (g : B' →bᵢ B'') :
    (formalVertexAxiomsHom B' B'' hB' hB'' g).comp (formalVertexAxiomsHom B B' hB hB' f) =
      formalVertexAxiomsHom B B'' hB hB'' (g.comp f) :=
  FormalVertexAxioms.Hom.ext fun p ↦ by
    simp [← AlgHom.comp_apply, SymmetricAlgebra.map_comp_map, Finsupp.mapRange.linearMap_comp]

end Map

end HeisenbergFockSpace

/-- Over a `ℚ`-algebra the Fock space has unique divisibility, so it carries the Heisenberg vertex
algebra structure `TauCeti.HeisenbergFockSpace.formalVertexAxioms`. -/
instance {R H : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup H] [Module R H] :
    HasUniqueDiv (HeisenbergFockSpace R H) :=
  letI : Module ℚ (HeisenbergFockSpace R H) := Module.compHom _ (algebraMap ℚ R)
  HasUniqueDiv.of_module_rat _

end TauCeti
