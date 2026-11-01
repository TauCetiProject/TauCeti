/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WeilRestriction.Basic
public import TauCeti.RingTheory.Etale.Galois

/-!
# Splitting of a Weil restriction over a separably closed field

Let `K` be a field, `B` a finite étale `K`-algebra (for instance a finite separable field
extension `K'/K`), `C` a `B`-algebra of finite presentation and `Ω` a separably closed field
containing `K`. The points of the Weil restriction `Res_{B/K} C` with values in `Ω` are the
`B`-algebra maps `C → B ⊗[K] Ω` (`WeilRestriction.homEquiv`). Over `Ω` the algebra `B` splits:
`B ⊗[K] Ω` is the product of copies of `Ω` indexed by the `K`-algebra maps `τ : B → Ω`, through
`b ⊗ ω ↦ (τ b * ω)_τ`. Hence

  `(Res_{B/K} C)(Ω) ≃ ∏_τ C_τ(Ω)`,

where `C_τ(Ω)` is the set of `Ω`-points of `C` for the `B`-algebra structure on `Ω` given by `τ`,
that is, of ring maps `f : C → Ω` with `f ∘ algebraMap B C = τ`. This is the statement on
`Ω`-points that over `Ω` the Weil restriction is the product of the conjugates of `Spec C` by the
embeddings of `B`; the corresponding isomorphism of `Ω`-algebras is not constructed here. An
automorphism `σ` of `Ω` over `K` acts on both sides: on points of the Weil restriction by
postcomposition, and on the tuples by permuting the factors and applying `σ`, the `τ`-component of
the image of a point being `σ` composed with its `σ⁻¹ • τ`-component.

Over a separable closure, this splitting compares a Weil restriction with the product of the
conjugates of `C`, as needed for the dimension, the reductivity and the character lattices of Weil
restrictions. Over a field an étale algebra is finite; the instance `Module.Finite K B` is
the one through which the Weil restriction is formed.

## Main declarations

* `TauCeti.Algebra.WeilRestriction.splittingEquiv K B C Ω`: the bijection between the `Ω`-points of
  `Res_{B/K} C` and the tuples, indexed by the `K`-algebra maps `τ : B → Ω`, of `Ω`-points of `C`
  lying over `τ`.
* `TauCeti.Algebra.WeilRestriction.splittingEquiv_apply`: the `τ`-component of a point `x` is the
  point `homEquiv x` of `C` followed by `b ⊗ ω ↦ τ b * ω`.
* `TauCeti.Algebra.WeilRestriction.productMap_homEquiv_splittingEquiv_symm_apply`: the inverse
  sends a family `f` to the point whose `τ`-component is `f τ`.
* `TauCeti.Algebra.WeilRestriction.splittingEquiv_comp_map`: the splitting is natural in `C`.
* `TauCeti.Algebra.WeilRestriction.splittingEquiv_algEquiv_comp`: the splitting is equivariant for
  the automorphisms of `Ω` over `K`.

## References

* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local II*, Publ. Math. IHÉS 60 (1984),
  1.5.14–1.5.16, pp. 30–31.
* J. S. Milne, *Algebraic Groups*, Cambridge Stud. Adv. Math. 170 (2017), Lem. 14.39, p. 238.
-/

public section

open scoped TensorProduct

namespace TauCeti.Algebra.WeilRestriction

variable (K B C Ω : Type*) [Field K] [CommRing B] [Algebra K B] [Module.Finite K B]
  [Algebra.Etale K B] [CommRing C] [Algebra B C] [Algebra.FinitePresentation B C] [Field Ω]
  [Algebra K Ω] [IsSepClosed Ω]

/-- **Splitting of a Weil restriction.** For a finite étale algebra `B` over a field `K`, a
finitely presented `B`-algebra `C` and a separably closed field `Ω` over `K`, the `Ω`-points of the
Weil restriction `Res_{B/K} C` correspond to the families, indexed by the `K`-algebra maps
`τ : B → Ω`, of `Ω`-points of `C` over `τ`, that is, of ring maps `C → Ω` extending `τ`. The
`τ`-component of a point `x` is `homEquiv x` followed by `b ⊗ ω ↦ τ b * ω`
(`splittingEquiv_apply`). -/
noncomputable def splittingEquiv :
    (WeilRestriction K B C →ₐ[K] Ω) ≃
      ((τ : B →ₐ[K] Ω) → {f : C →+* Ω // f.comp (algebraMap B C) = τ}) :=
  (homEquiv K B C Ω).trans (Algebra.Etale.algHomTensorProductEquivPi K Ω B C)

variable {K B C Ω}

/-- The `τ`-component of `splittingEquiv x` sends `c` to the image of `homEquiv x c` under
`b ⊗ ω ↦ τ b * ω`. -/
@[simp]
theorem splittingEquiv_apply (x : WeilRestriction K B C →ₐ[K] Ω) (τ : B →ₐ[K] Ω) (c : C) :
    (splittingEquiv K B C Ω x τ : C →+* Ω) c =
      Algebra.TensorProduct.productMap τ (AlgHom.id K Ω) (homEquiv K B C Ω x c) := by
  rw [splittingEquiv, Equiv.trans_apply, Algebra.Etale.algHomTensorProductEquivPi_apply]

/-- The point of `Res_{B/K} C` attached to a family `f` of points has `τ`-component `f τ`:
following `homEquiv` of it by `b ⊗ ω ↦ τ b * ω` gives `f τ`. This is not a `simp` lemma, since
`simp` unfolds `homEquiv` on its left-hand side through `homEquiv_apply`. -/
theorem productMap_homEquiv_splittingEquiv_symm_apply
    (f : (τ : B →ₐ[K] Ω) → {f : C →+* Ω // f.comp (algebraMap B C) = τ}) (τ : B →ₐ[K] Ω)
    (c : C) :
    Algebra.TensorProduct.productMap τ (AlgHom.id K Ω)
      (homEquiv K B C Ω ((splittingEquiv K B C Ω).symm f) c) = (f τ : C →+* Ω) c := by
  rw [← splittingEquiv_apply, Equiv.apply_symm_apply]

/-- **Naturality of the splitting in `C`.** The components of the image of a point under the
map of Weil restrictions induced by `φ : C →ₐ[B] D` are the components of the point composed
with `φ`. -/
theorem splittingEquiv_comp_map {D : Type*} [CommRing D] [Algebra B D]
    [Algebra.FinitePresentation B D] (φ : C →ₐ[B] D) (x : WeilRestriction K B D →ₐ[K] Ω)
    (τ : B →ₐ[K] Ω) :
    (splittingEquiv K B C Ω (x.comp (map K B φ)) τ : C →+* Ω) =
      (splittingEquiv K B D Ω x τ : D →+* Ω).comp φ := by
  ext c
  simp only [RingHom.comp_apply, splittingEquiv_apply, homEquiv_comp_map, AlgHom.comp_apply,
    RingHom.coe_coe]

/-- **Galois equivariance of the splitting.** An automorphism `σ` of `Ω` over `K` acts on the
`Ω`-points of `Res_{B/K} C` by postcomposition. The `τ`-component of the image of a point `x` is
`σ` composed with the `σ⁻¹ • τ`-component of `x`. -/
theorem splittingEquiv_algEquiv_comp (σ : Ω ≃ₐ[K] Ω) (x : WeilRestriction K B C →ₐ[K] Ω)
    (τ : B →ₐ[K] Ω) :
    (splittingEquiv K B C Ω ((σ : Ω →ₐ[K] Ω).comp x) τ : C →+* Ω) =
      (σ : Ω →+* Ω).comp (splittingEquiv K B C Ω x (σ⁻¹ • τ)) := by
  rw [splittingEquiv, Equiv.trans_apply, homEquiv_comp]
  exact Algebra.Etale.algHomTensorProductEquivPi_lTensor σ _ τ

end TauCeti.Algebra.WeilRestriction
