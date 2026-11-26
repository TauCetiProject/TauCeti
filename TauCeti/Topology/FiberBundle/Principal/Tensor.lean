/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Principal.Extension
public import TauCeti.Topology.FiberBundle.Principal.Prod
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Inverse and tensor product of principal bundles with commutative structure group

For a commutative topological group `G`, inversion `g ↦ g⁻¹` and multiplication
`(g, h) ↦ g h` are continuous homomorphisms (Mathlib's `ContinuousMonoidHom.inv` and
`ContinuousMonoidHom.mul`). Extending structure group along them
(`TauCeti.PrincipalBundle.Extend`) gives

* the **inverse** `P⁻¹ = P ×_{g ↦ g⁻¹} G` of a principal `G`-bundle `P`
  (`TauCeti.PrincipalBundle.Inverse`);
* the **tensor product** `P ⊗ Q = (P ×_B Q) ×_{(g, h) ↦ g h} G` of two principal `G`-bundles
  (`TauCeti.PrincipalBundle.Tensor`), the extension of their fibre product
  (`TauCeti.PrincipalBundle.FiberProd`).

For `G = U(1)` these are the inverse and the tensor product of the associated complex lines. Both
are abbreviations, so the `Extend` API (`Extend.inl`, `Extend.mk`, `Extend.smul_inl`, the
principal bundle instance) applies to them directly.

## Main definitions

* `TauCeti.PrincipalBundle.Inverse`: the inverse of a principal `G`-bundle.
* `TauCeti.PrincipalBundle.Tensor`: the tensor product of two principal `G`-bundles.

## References

* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 6, §§2–3.
-/

public section

open Bundle

namespace TauCeti.PrincipalBundle

variable {B : Type*} [TopologicalSpace B] (G : Type*) [CommGroup G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The **inverse** `P⁻¹ = P ×_{g ↦ g⁻¹} G` of a principal `G`-bundle `P` for a commutative
topological group `G`: the extension of `P` along inversion. A point `p` of `P` gives the point
`[p, 1]` (`TauCeti.PrincipalBundle.Extend.inl`), and `[p • g, 1] = [p, 1] • g⁻¹`
(`TauCeti.PrincipalBundle.Extend.inl_smul`). -/
abbrev Inverse (P : B → Type*) [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
    [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P] : B → Type _ :=
  Extend P (ContinuousMonoidHom.inv G : G →* G) (map_continuous (ContinuousMonoidHom.inv G))

/-- The **tensor product** `P ⊗ Q = (P ×_B Q) ×_{(g, h) ↦ g h} G` of two principal `G`-bundles
`P` and `Q` for a commutative topological group `G`: the extension of the fibre product
`TauCeti.PrincipalBundle.FiberProd P Q` along multiplication `G × G → G`. A pair `(p, q)` gives
the point `[(p, q), 1]`, and `[(p • g, q • h), 1] = [(p, q), 1] • (g h)`
(`TauCeti.PrincipalBundle.Extend.inl_smul`). -/
abbrev Tensor (P Q : B → Type*) [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
    [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
    [TopologicalSpace (TotalSpace G Q)] [∀ b, TopologicalSpace (Q b)] [FiberBundle G Q]
    [∀ b, MulAction Gᵐᵒᵖ (Q b)] [PrincipalBundle G Q] : B → Type _ :=
  Extend (FiberProd P Q) (ContinuousMonoidHom.mul G : G × G →* G)
    (map_continuous (ContinuousMonoidHom.mul G))

end TauCeti.PrincipalBundle
